-- Prove2me | solution 1 for Brocard.berndt_galway_group_078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:19:19.68051+00:00
-- url     : https://prove2.me/submissions/577206be-c0f5-4745-b61f-ce3ab9e40c3d

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_3571
import Theorems.Thm_Brocard_berndt_galway_chunk_3572
import Theorems.Thm_Brocard_berndt_galway_chunk_3573
import Theorems.Thm_Brocard_berndt_galway_chunk_3574
import Theorems.Thm_Brocard_berndt_galway_chunk_3575
import Theorems.Thm_Brocard_berndt_galway_chunk_3576
import Theorems.Thm_Brocard_berndt_galway_chunk_3577
import Theorems.Thm_Brocard_berndt_galway_chunk_3578
import Theorems.Thm_Brocard_berndt_galway_chunk_3579
import Theorems.Thm_Brocard_berndt_galway_chunk_3580
import Theorems.Thm_Brocard_berndt_galway_chunk_3581
import Theorems.Thm_Brocard_berndt_galway_chunk_3582
import Theorems.Thm_Brocard_berndt_galway_chunk_3583
import Theorems.Thm_Brocard_berndt_galway_chunk_3584
import Theorems.Thm_Brocard_berndt_galway_chunk_3585
import Theorems.Thm_Brocard_berndt_galway_chunk_3586
import Theorems.Thm_Brocard_berndt_galway_chunk_3587
import Theorems.Thm_Brocard_berndt_galway_chunk_3588
import Theorems.Thm_Brocard_berndt_galway_chunk_3589
import Theorems.Thm_Brocard_berndt_galway_chunk_3590
import Theorems.Thm_Brocard_berndt_galway_chunk_3591
import Theorems.Thm_Brocard_berndt_galway_chunk_3592
import Theorems.Thm_Brocard_berndt_galway_chunk_3593
import Theorems.Thm_Brocard_berndt_galway_chunk_3594
import Theorems.Thm_Brocard_berndt_galway_chunk_3595
import Theorems.Thm_Brocard_berndt_galway_chunk_3596
import Theorems.Thm_Brocard_berndt_galway_chunk_3597
import Theorems.Thm_Brocard_berndt_galway_chunk_3598
import Theorems.Thm_Brocard_berndt_galway_chunk_3599
import Theorems.Thm_Brocard_berndt_galway_chunk_3600
import Theorems.Thm_Brocard_berndt_galway_chunk_3601
import Theorems.Thm_Brocard_berndt_galway_chunk_3602
import Theorems.Thm_Brocard_berndt_galway_chunk_3603
import Theorems.Thm_Brocard_berndt_galway_chunk_3604
import Theorems.Thm_Brocard_berndt_galway_chunk_3605
import Theorems.Thm_Brocard_berndt_galway_chunk_3606
import Theorems.Thm_Brocard_berndt_galway_chunk_3607
import Theorems.Thm_Brocard_berndt_galway_chunk_3608
import Theorems.Thm_Brocard_berndt_galway_chunk_3609
import Theorems.Thm_Brocard_berndt_galway_chunk_3610
import Theorems.Thm_Brocard_berndt_galway_chunk_3611
import Theorems.Thm_Brocard_berndt_galway_chunk_3612
import Theorems.Thm_Brocard_berndt_galway_chunk_3613
import Theorems.Thm_Brocard_berndt_galway_chunk_3614
import Theorems.Thm_Brocard_berndt_galway_chunk_3615
import Theorems.Thm_Brocard_berndt_galway_chunk_3616

theorem solution (n m : ℕ) (h1 : 642086330 ≤ n) (h2 : n < 650359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 646223021 with hs0 | hs0
  · -- n < 646223021
    rcases Nat.lt_or_ge n 644244604 with hs1 | hs1
    · -- n < 644244604
      rcases Nat.lt_or_ge n 643165467 with hs2 | hs2
      · -- n < 643165467
        rcases Nat.lt_or_ge n 642625899 with hs3 | hs3
        · -- n < 642625899
          rcases Nat.lt_or_ge n 642446043 with hs4 | hs4
          · -- n < 642446043
            rcases Nat.lt_or_ge n 642266187 with hs5 | hs5
            · -- n < 642266187
              exact Brocard.berndt_galway_chunk_3571 n m (by omega) (by omega) h
            · -- n >= 642266187
              exact Brocard.berndt_galway_chunk_3572 n m (by omega) (by omega) h
          · -- n >= 642446043
            exact Brocard.berndt_galway_chunk_3573 n m (by omega) (by omega) h
        · -- n >= 642625899
          rcases Nat.lt_or_ge n 642985611 with hs4 | hs4
          · -- n < 642985611
            rcases Nat.lt_or_ge n 642805755 with hs5 | hs5
            · -- n < 642805755
              exact Brocard.berndt_galway_chunk_3574 n m (by omega) (by omega) h
            · -- n >= 642805755
              exact Brocard.berndt_galway_chunk_3575 n m (by omega) (by omega) h
          · -- n >= 642985611
            exact Brocard.berndt_galway_chunk_3576 n m (by omega) (by omega) h
      · -- n >= 643165467
        rcases Nat.lt_or_ge n 643705035 with hs3 | hs3
        · -- n < 643705035
          rcases Nat.lt_or_ge n 643525179 with hs4 | hs4
          · -- n < 643525179
            rcases Nat.lt_or_ge n 643345323 with hs5 | hs5
            · -- n < 643345323
              exact Brocard.berndt_galway_chunk_3577 n m (by omega) (by omega) h
            · -- n >= 643345323
              exact Brocard.berndt_galway_chunk_3578 n m (by omega) (by omega) h
          · -- n >= 643525179
            exact Brocard.berndt_galway_chunk_3579 n m (by omega) (by omega) h
        · -- n >= 643705035
          rcases Nat.lt_or_ge n 644064748 with hs4 | hs4
          · -- n < 644064748
            rcases Nat.lt_or_ge n 643884892 with hs5 | hs5
            · -- n < 643884892
              exact Brocard.berndt_galway_chunk_3580 n m (by omega) (by omega) h
            · -- n >= 643884892
              exact Brocard.berndt_galway_chunk_3581 n m (by omega) (by omega) h
          · -- n >= 644064748
            exact Brocard.berndt_galway_chunk_3582 n m (by omega) (by omega) h
    · -- n >= 644244604
      rcases Nat.lt_or_ge n 645323741 with hs2 | hs2
      · -- n < 645323741
        rcases Nat.lt_or_ge n 644784172 with hs3 | hs3
        · -- n < 644784172
          rcases Nat.lt_or_ge n 644604316 with hs4 | hs4
          · -- n < 644604316
            rcases Nat.lt_or_ge n 644424460 with hs5 | hs5
            · -- n < 644424460
              exact Brocard.berndt_galway_chunk_3583 n m (by omega) (by omega) h
            · -- n >= 644424460
              exact Brocard.berndt_galway_chunk_3584 n m (by omega) (by omega) h
          · -- n >= 644604316
            exact Brocard.berndt_galway_chunk_3585 n m (by omega) (by omega) h
        · -- n >= 644784172
          rcases Nat.lt_or_ge n 645143884 with hs4 | hs4
          · -- n < 645143884
            rcases Nat.lt_or_ge n 644964028 with hs5 | hs5
            · -- n < 644964028
              exact Brocard.berndt_galway_chunk_3586 n m (by omega) (by omega) h
            · -- n >= 644964028
              exact Brocard.berndt_galway_chunk_3587 n m (by omega) (by omega) h
          · -- n >= 645143884
            exact Brocard.berndt_galway_chunk_3588 n m (by omega) (by omega) h
      · -- n >= 645323741
        rcases Nat.lt_or_ge n 645863309 with hs3 | hs3
        · -- n < 645863309
          rcases Nat.lt_or_ge n 645683453 with hs4 | hs4
          · -- n < 645683453
            rcases Nat.lt_or_ge n 645503597 with hs5 | hs5
            · -- n < 645503597
              exact Brocard.berndt_galway_chunk_3589 n m (by omega) (by omega) h
            · -- n >= 645503597
              exact Brocard.berndt_galway_chunk_3590 n m (by omega) (by omega) h
          · -- n >= 645683453
            exact Brocard.berndt_galway_chunk_3591 n m (by omega) (by omega) h
        · -- n >= 645863309
          rcases Nat.lt_or_ge n 646043165 with hs4 | hs4
          · -- n < 646043165
            exact Brocard.berndt_galway_chunk_3592 n m (by omega) (by omega) h
          · -- n >= 646043165
            exact Brocard.berndt_galway_chunk_3593 n m (by omega) (by omega) h
  · -- n >= 646223021
    rcases Nat.lt_or_ge n 648381294 with hs1 | hs1
    · -- n < 648381294
      rcases Nat.lt_or_ge n 647302158 with hs2 | hs2
      · -- n < 647302158
        rcases Nat.lt_or_ge n 646762589 with hs3 | hs3
        · -- n < 646762589
          rcases Nat.lt_or_ge n 646582733 with hs4 | hs4
          · -- n < 646582733
            rcases Nat.lt_or_ge n 646402877 with hs5 | hs5
            · -- n < 646402877
              exact Brocard.berndt_galway_chunk_3594 n m (by omega) (by omega) h
            · -- n >= 646402877
              exact Brocard.berndt_galway_chunk_3595 n m (by omega) (by omega) h
          · -- n >= 646582733
            exact Brocard.berndt_galway_chunk_3596 n m (by omega) (by omega) h
        · -- n >= 646762589
          rcases Nat.lt_or_ge n 647122302 with hs4 | hs4
          · -- n < 647122302
            rcases Nat.lt_or_ge n 646942446 with hs5 | hs5
            · -- n < 646942446
              exact Brocard.berndt_galway_chunk_3597 n m (by omega) (by omega) h
            · -- n >= 646942446
              exact Brocard.berndt_galway_chunk_3598 n m (by omega) (by omega) h
          · -- n >= 647122302
            exact Brocard.berndt_galway_chunk_3599 n m (by omega) (by omega) h
      · -- n >= 647302158
        rcases Nat.lt_or_ge n 647841726 with hs3 | hs3
        · -- n < 647841726
          rcases Nat.lt_or_ge n 647661870 with hs4 | hs4
          · -- n < 647661870
            rcases Nat.lt_or_ge n 647482014 with hs5 | hs5
            · -- n < 647482014
              exact Brocard.berndt_galway_chunk_3600 n m (by omega) (by omega) h
            · -- n >= 647482014
              exact Brocard.berndt_galway_chunk_3601 n m (by omega) (by omega) h
          · -- n >= 647661870
            exact Brocard.berndt_galway_chunk_3602 n m (by omega) (by omega) h
        · -- n >= 647841726
          rcases Nat.lt_or_ge n 648201438 with hs4 | hs4
          · -- n < 648201438
            rcases Nat.lt_or_ge n 648021582 with hs5 | hs5
            · -- n < 648021582
              exact Brocard.berndt_galway_chunk_3603 n m (by omega) (by omega) h
            · -- n >= 648021582
              exact Brocard.berndt_galway_chunk_3604 n m (by omega) (by omega) h
          · -- n >= 648201438
            exact Brocard.berndt_galway_chunk_3605 n m (by omega) (by omega) h
    · -- n >= 648381294
      rcases Nat.lt_or_ge n 649460431 with hs2 | hs2
      · -- n < 649460431
        rcases Nat.lt_or_ge n 648920863 with hs3 | hs3
        · -- n < 648920863
          rcases Nat.lt_or_ge n 648741007 with hs4 | hs4
          · -- n < 648741007
            rcases Nat.lt_or_ge n 648561151 with hs5 | hs5
            · -- n < 648561151
              exact Brocard.berndt_galway_chunk_3606 n m (by omega) (by omega) h
            · -- n >= 648561151
              exact Brocard.berndt_galway_chunk_3607 n m (by omega) (by omega) h
          · -- n >= 648741007
            exact Brocard.berndt_galway_chunk_3608 n m (by omega) (by omega) h
        · -- n >= 648920863
          rcases Nat.lt_or_ge n 649280575 with hs4 | hs4
          · -- n < 649280575
            rcases Nat.lt_or_ge n 649100719 with hs5 | hs5
            · -- n < 649100719
              exact Brocard.berndt_galway_chunk_3609 n m (by omega) (by omega) h
            · -- n >= 649100719
              exact Brocard.berndt_galway_chunk_3610 n m (by omega) (by omega) h
          · -- n >= 649280575
            exact Brocard.berndt_galway_chunk_3611 n m (by omega) (by omega) h
      · -- n >= 649460431
        rcases Nat.lt_or_ge n 650000000 with hs3 | hs3
        · -- n < 650000000
          rcases Nat.lt_or_ge n 649820143 with hs4 | hs4
          · -- n < 649820143
            rcases Nat.lt_or_ge n 649640287 with hs5 | hs5
            · -- n < 649640287
              exact Brocard.berndt_galway_chunk_3612 n m (by omega) (by omega) h
            · -- n >= 649640287
              exact Brocard.berndt_galway_chunk_3613 n m (by omega) (by omega) h
          · -- n >= 649820143
            exact Brocard.berndt_galway_chunk_3614 n m (by omega) (by omega) h
        · -- n >= 650000000
          rcases Nat.lt_or_ge n 650179856 with hs4 | hs4
          · -- n < 650179856
            exact Brocard.berndt_galway_chunk_3615 n m (by omega) (by omega) h
          · -- n >= 650179856
            exact Brocard.berndt_galway_chunk_3616 n m (by omega) (by omega) h
