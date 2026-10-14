-- Prove2me | solution 1 for Brocard.berndt_galway_group_013
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:51:30.458993+00:00
-- url     : https://prove2.me/submissions/f33fe4e1-d133-4894-8473-a8403d0bf16e

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0557
import Theorems.Thm_Brocard_berndt_galway_chunk_0558
import Theorems.Thm_Brocard_berndt_galway_chunk_0559
import Theorems.Thm_Brocard_berndt_galway_chunk_0560
import Theorems.Thm_Brocard_berndt_galway_chunk_0561
import Theorems.Thm_Brocard_berndt_galway_chunk_0562
import Theorems.Thm_Brocard_berndt_galway_chunk_0563
import Theorems.Thm_Brocard_berndt_galway_chunk_0564
import Theorems.Thm_Brocard_berndt_galway_chunk_0565
import Theorems.Thm_Brocard_berndt_galway_chunk_0566
import Theorems.Thm_Brocard_berndt_galway_chunk_0567
import Theorems.Thm_Brocard_berndt_galway_chunk_0568
import Theorems.Thm_Brocard_berndt_galway_chunk_0569
import Theorems.Thm_Brocard_berndt_galway_chunk_0570
import Theorems.Thm_Brocard_berndt_galway_chunk_0571
import Theorems.Thm_Brocard_berndt_galway_chunk_0572
import Theorems.Thm_Brocard_berndt_galway_chunk_0573
import Theorems.Thm_Brocard_berndt_galway_chunk_0574
import Theorems.Thm_Brocard_berndt_galway_chunk_0575
import Theorems.Thm_Brocard_berndt_galway_chunk_0576
import Theorems.Thm_Brocard_berndt_galway_chunk_0577
import Theorems.Thm_Brocard_berndt_galway_chunk_0578
import Theorems.Thm_Brocard_berndt_galway_chunk_0579
import Theorems.Thm_Brocard_berndt_galway_chunk_0580
import Theorems.Thm_Brocard_berndt_galway_chunk_0581
import Theorems.Thm_Brocard_berndt_galway_chunk_0582
import Theorems.Thm_Brocard_berndt_galway_chunk_0583
import Theorems.Thm_Brocard_berndt_galway_chunk_0584
import Theorems.Thm_Brocard_berndt_galway_chunk_0585
import Theorems.Thm_Brocard_berndt_galway_chunk_0586
import Theorems.Thm_Brocard_berndt_galway_chunk_0587
import Theorems.Thm_Brocard_berndt_galway_chunk_0588
import Theorems.Thm_Brocard_berndt_galway_chunk_0589
import Theorems.Thm_Brocard_berndt_galway_chunk_0590
import Theorems.Thm_Brocard_berndt_galway_chunk_0591
import Theorems.Thm_Brocard_berndt_galway_chunk_0592
import Theorems.Thm_Brocard_berndt_galway_chunk_0593
import Theorems.Thm_Brocard_berndt_galway_chunk_0594
import Theorems.Thm_Brocard_berndt_galway_chunk_0595
import Theorems.Thm_Brocard_berndt_galway_chunk_0596
import Theorems.Thm_Brocard_berndt_galway_chunk_0597
import Theorems.Thm_Brocard_berndt_galway_chunk_0598
import Theorems.Thm_Brocard_berndt_galway_chunk_0599
import Theorems.Thm_Brocard_berndt_galway_chunk_0600
import Theorems.Thm_Brocard_berndt_galway_chunk_0601
import Theorems.Thm_Brocard_berndt_galway_chunk_0602
import Theorems.Thm_Brocard_berndt_galway_chunk_0603

theorem solution (n m : ℕ) (h1 : 100000000 ≤ n) (h2 : n < 108453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 104316546 with hs0 | hs0
  · -- n < 104316546
    rcases Nat.lt_or_ge n 102158273 with hs1 | hs1
    · -- n < 102158273
      rcases Nat.lt_or_ge n 101079136 with hs2 | hs2
      · -- n < 101079136
        rcases Nat.lt_or_ge n 100539568 with hs3 | hs3
        · -- n < 100539568
          rcases Nat.lt_or_ge n 100359712 with hs4 | hs4
          · -- n < 100359712
            rcases Nat.lt_or_ge n 100179856 with hs5 | hs5
            · -- n < 100179856
              exact Brocard.berndt_galway_chunk_0557 n m (by omega) (by omega) h
            · -- n >= 100179856
              exact Brocard.berndt_galway_chunk_0558 n m (by omega) (by omega) h
          · -- n >= 100359712
            exact Brocard.berndt_galway_chunk_0559 n m (by omega) (by omega) h
        · -- n >= 100539568
          rcases Nat.lt_or_ge n 100899280 with hs4 | hs4
          · -- n < 100899280
            rcases Nat.lt_or_ge n 100719424 with hs5 | hs5
            · -- n < 100719424
              exact Brocard.berndt_galway_chunk_0560 n m (by omega) (by omega) h
            · -- n >= 100719424
              exact Brocard.berndt_galway_chunk_0561 n m (by omega) (by omega) h
          · -- n >= 100899280
            exact Brocard.berndt_galway_chunk_0562 n m (by omega) (by omega) h
      · -- n >= 101079136
        rcases Nat.lt_or_ge n 101618705 with hs3 | hs3
        · -- n < 101618705
          rcases Nat.lt_or_ge n 101438848 with hs4 | hs4
          · -- n < 101438848
            rcases Nat.lt_or_ge n 101258992 with hs5 | hs5
            · -- n < 101258992
              exact Brocard.berndt_galway_chunk_0563 n m (by omega) (by omega) h
            · -- n >= 101258992
              exact Brocard.berndt_galway_chunk_0564 n m (by omega) (by omega) h
          · -- n >= 101438848
            exact Brocard.berndt_galway_chunk_0565 n m (by omega) (by omega) h
        · -- n >= 101618705
          rcases Nat.lt_or_ge n 101978417 with hs4 | hs4
          · -- n < 101978417
            rcases Nat.lt_or_ge n 101798561 with hs5 | hs5
            · -- n < 101798561
              exact Brocard.berndt_galway_chunk_0566 n m (by omega) (by omega) h
            · -- n >= 101798561
              exact Brocard.berndt_galway_chunk_0567 n m (by omega) (by omega) h
          · -- n >= 101978417
            exact Brocard.berndt_galway_chunk_0568 n m (by omega) (by omega) h
    · -- n >= 102158273
      rcases Nat.lt_or_ge n 103237410 with hs2 | hs2
      · -- n < 103237410
        rcases Nat.lt_or_ge n 102697841 with hs3 | hs3
        · -- n < 102697841
          rcases Nat.lt_or_ge n 102517985 with hs4 | hs4
          · -- n < 102517985
            rcases Nat.lt_or_ge n 102338129 with hs5 | hs5
            · -- n < 102338129
              exact Brocard.berndt_galway_chunk_0569 n m (by omega) (by omega) h
            · -- n >= 102338129
              exact Brocard.berndt_galway_chunk_0570 n m (by omega) (by omega) h
          · -- n >= 102517985
            exact Brocard.berndt_galway_chunk_0571 n m (by omega) (by omega) h
        · -- n >= 102697841
          rcases Nat.lt_or_ge n 103057553 with hs4 | hs4
          · -- n < 103057553
            rcases Nat.lt_or_ge n 102877697 with hs5 | hs5
            · -- n < 102877697
              exact Brocard.berndt_galway_chunk_0572 n m (by omega) (by omega) h
            · -- n >= 102877697
              exact Brocard.berndt_galway_chunk_0573 n m (by omega) (by omega) h
          · -- n >= 103057553
            exact Brocard.berndt_galway_chunk_0574 n m (by omega) (by omega) h
      · -- n >= 103237410
        rcases Nat.lt_or_ge n 103776978 with hs3 | hs3
        · -- n < 103776978
          rcases Nat.lt_or_ge n 103597122 with hs4 | hs4
          · -- n < 103597122
            rcases Nat.lt_or_ge n 103417266 with hs5 | hs5
            · -- n < 103417266
              exact Brocard.berndt_galway_chunk_0575 n m (by omega) (by omega) h
            · -- n >= 103417266
              exact Brocard.berndt_galway_chunk_0576 n m (by omega) (by omega) h
          · -- n >= 103597122
            exact Brocard.berndt_galway_chunk_0577 n m (by omega) (by omega) h
        · -- n >= 103776978
          rcases Nat.lt_or_ge n 104136690 with hs4 | hs4
          · -- n < 104136690
            rcases Nat.lt_or_ge n 103956834 with hs5 | hs5
            · -- n < 103956834
              exact Brocard.berndt_galway_chunk_0578 n m (by omega) (by omega) h
            · -- n >= 103956834
              exact Brocard.berndt_galway_chunk_0579 n m (by omega) (by omega) h
          · -- n >= 104136690
            exact Brocard.berndt_galway_chunk_0580 n m (by omega) (by omega) h
  · -- n >= 104316546
    rcases Nat.lt_or_ge n 106474820 with hs1 | hs1
    · -- n < 106474820
      rcases Nat.lt_or_ge n 105395683 with hs2 | hs2
      · -- n < 105395683
        rcases Nat.lt_or_ge n 104856115 with hs3 | hs3
        · -- n < 104856115
          rcases Nat.lt_or_ge n 104676258 with hs4 | hs4
          · -- n < 104676258
            rcases Nat.lt_or_ge n 104496402 with hs5 | hs5
            · -- n < 104496402
              exact Brocard.berndt_galway_chunk_0581 n m (by omega) (by omega) h
            · -- n >= 104496402
              exact Brocard.berndt_galway_chunk_0582 n m (by omega) (by omega) h
          · -- n >= 104676258
            exact Brocard.berndt_galway_chunk_0583 n m (by omega) (by omega) h
        · -- n >= 104856115
          rcases Nat.lt_or_ge n 105215827 with hs4 | hs4
          · -- n < 105215827
            rcases Nat.lt_or_ge n 105035971 with hs5 | hs5
            · -- n < 105035971
              exact Brocard.berndt_galway_chunk_0584 n m (by omega) (by omega) h
            · -- n >= 105035971
              exact Brocard.berndt_galway_chunk_0585 n m (by omega) (by omega) h
          · -- n >= 105215827
            exact Brocard.berndt_galway_chunk_0586 n m (by omega) (by omega) h
      · -- n >= 105395683
        rcases Nat.lt_or_ge n 105935251 with hs3 | hs3
        · -- n < 105935251
          rcases Nat.lt_or_ge n 105755395 with hs4 | hs4
          · -- n < 105755395
            rcases Nat.lt_or_ge n 105575539 with hs5 | hs5
            · -- n < 105575539
              exact Brocard.berndt_galway_chunk_0587 n m (by omega) (by omega) h
            · -- n >= 105575539
              exact Brocard.berndt_galway_chunk_0588 n m (by omega) (by omega) h
          · -- n >= 105755395
            exact Brocard.berndt_galway_chunk_0589 n m (by omega) (by omega) h
        · -- n >= 105935251
          rcases Nat.lt_or_ge n 106294964 with hs4 | hs4
          · -- n < 106294964
            rcases Nat.lt_or_ge n 106115107 with hs5 | hs5
            · -- n < 106115107
              exact Brocard.berndt_galway_chunk_0590 n m (by omega) (by omega) h
            · -- n >= 106115107
              exact Brocard.berndt_galway_chunk_0591 n m (by omega) (by omega) h
          · -- n >= 106294964
            exact Brocard.berndt_galway_chunk_0592 n m (by omega) (by omega) h
    · -- n >= 106474820
      rcases Nat.lt_or_ge n 107553956 with hs2 | hs2
      · -- n < 107553956
        rcases Nat.lt_or_ge n 107014388 with hs3 | hs3
        · -- n < 107014388
          rcases Nat.lt_or_ge n 106834532 with hs4 | hs4
          · -- n < 106834532
            rcases Nat.lt_or_ge n 106654676 with hs5 | hs5
            · -- n < 106654676
              exact Brocard.berndt_galway_chunk_0593 n m (by omega) (by omega) h
            · -- n >= 106654676
              exact Brocard.berndt_galway_chunk_0594 n m (by omega) (by omega) h
          · -- n >= 106834532
            exact Brocard.berndt_galway_chunk_0595 n m (by omega) (by omega) h
        · -- n >= 107014388
          rcases Nat.lt_or_ge n 107374100 with hs4 | hs4
          · -- n < 107374100
            rcases Nat.lt_or_ge n 107194244 with hs5 | hs5
            · -- n < 107194244
              exact Brocard.berndt_galway_chunk_0596 n m (by omega) (by omega) h
            · -- n >= 107194244
              exact Brocard.berndt_galway_chunk_0597 n m (by omega) (by omega) h
          · -- n >= 107374100
            exact Brocard.berndt_galway_chunk_0598 n m (by omega) (by omega) h
      · -- n >= 107553956
        rcases Nat.lt_or_ge n 108093525 with hs3 | hs3
        · -- n < 108093525
          rcases Nat.lt_or_ge n 107913669 with hs4 | hs4
          · -- n < 107913669
            rcases Nat.lt_or_ge n 107733812 with hs5 | hs5
            · -- n < 107733812
              exact Brocard.berndt_galway_chunk_0599 n m (by omega) (by omega) h
            · -- n >= 107733812
              exact Brocard.berndt_galway_chunk_0600 n m (by omega) (by omega) h
          · -- n >= 107913669
            exact Brocard.berndt_galway_chunk_0601 n m (by omega) (by omega) h
        · -- n >= 108093525
          rcases Nat.lt_or_ge n 108273381 with hs4 | hs4
          · -- n < 108273381
            exact Brocard.berndt_galway_chunk_0602 n m (by omega) (by omega) h
          · -- n >= 108273381
            exact Brocard.berndt_galway_chunk_0603 n m (by omega) (by omega) h
