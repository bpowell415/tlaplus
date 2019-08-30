------------------------- MODULE EulerMultiple3And5 -------------------------
EXTENDS Naturals, TLC

Mod3(r) == r % 3 = 0

Mod5(r) == r % 5 = 0

(* --algorithm EulerMultiple3And5
variables r = 1, r_sum = 0;
begin
       
    while r < 1000 do
        if Mod3(r) then
            r_sum := r_sum + r;
        elsif Mod5(r) then
            r_sum := r_sum + r;
        end if;
        r := r + 1;
    end while;
    print(r_sum);
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES r, r_sum, pc

vars == << r, r_sum, pc >>

Init == (* Global variables *)
        /\ r = 1
        /\ r_sum = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF r < 1000
               THEN /\ IF Mod3(r)
                          THEN /\ r_sum' = r_sum + r
                          ELSE /\ IF Mod5(r)
                                     THEN /\ r_sum' = r_sum + r
                                     ELSE /\ TRUE
                                          /\ r_sum' = r_sum
                    /\ r' = r + 1
                    /\ pc' = "Lbl_1"
               ELSE /\ PrintT((r_sum))
                    /\ pc' = "Done"
                    /\ UNCHANGED << r, r_sum >>

Next == Lbl_1
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Thu Aug 29 16:49:54 CDT 2019 by bpowe
\* Created Thu Aug 29 16:26:08 CDT 2019 by bpowe
