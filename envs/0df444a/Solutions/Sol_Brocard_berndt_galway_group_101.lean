-- Prove2me | solution 1 for Brocard.berndt_galway_group_101
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:32:23.39+00:00
-- url     : https://prove2.me/submissions/bafa6e9b-43db-4d86-9eac-6bf708c0cbb8

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4637
import Theorems.Thm_Brocard_berndt_galway_chunk_4638
import Theorems.Thm_Brocard_berndt_galway_chunk_4639
import Theorems.Thm_Brocard_berndt_galway_chunk_4640
import Theorems.Thm_Brocard_berndt_galway_chunk_4641
import Theorems.Thm_Brocard_berndt_galway_chunk_4642
import Theorems.Thm_Brocard_berndt_galway_chunk_4643
import Theorems.Thm_Brocard_berndt_galway_chunk_4644
import Theorems.Thm_Brocard_berndt_galway_chunk_4645
import Theorems.Thm_Brocard_berndt_galway_chunk_4646
import Theorems.Thm_Brocard_berndt_galway_chunk_4647
import Theorems.Thm_Brocard_berndt_galway_chunk_4648
import Theorems.Thm_Brocard_berndt_galway_chunk_4649
import Theorems.Thm_Brocard_berndt_galway_chunk_4650
import Theorems.Thm_Brocard_berndt_galway_chunk_4651
import Theorems.Thm_Brocard_berndt_galway_chunk_4652
import Theorems.Thm_Brocard_berndt_galway_chunk_4653
import Theorems.Thm_Brocard_berndt_galway_chunk_4654
import Theorems.Thm_Brocard_berndt_galway_chunk_4655
import Theorems.Thm_Brocard_berndt_galway_chunk_4656
import Theorems.Thm_Brocard_berndt_galway_chunk_4657
import Theorems.Thm_Brocard_berndt_galway_chunk_4658
import Theorems.Thm_Brocard_berndt_galway_chunk_4659
import Theorems.Thm_Brocard_berndt_galway_chunk_4660
import Theorems.Thm_Brocard_berndt_galway_chunk_4661
import Theorems.Thm_Brocard_berndt_galway_chunk_4662
import Theorems.Thm_Brocard_berndt_galway_chunk_4663
import Theorems.Thm_Brocard_berndt_galway_chunk_4664
import Theorems.Thm_Brocard_berndt_galway_chunk_4665
import Theorems.Thm_Brocard_berndt_galway_chunk_4666
import Theorems.Thm_Brocard_berndt_galway_chunk_4667
import Theorems.Thm_Brocard_berndt_galway_chunk_4668
import Theorems.Thm_Brocard_berndt_galway_chunk_4669
import Theorems.Thm_Brocard_berndt_galway_chunk_4670
import Theorems.Thm_Brocard_berndt_galway_chunk_4671
import Theorems.Thm_Brocard_berndt_galway_chunk_4672
import Theorems.Thm_Brocard_berndt_galway_chunk_4673
import Theorems.Thm_Brocard_berndt_galway_chunk_4674
import Theorems.Thm_Brocard_berndt_galway_chunk_4675
import Theorems.Thm_Brocard_berndt_galway_chunk_4676
import Theorems.Thm_Brocard_berndt_galway_chunk_4677
import Theorems.Thm_Brocard_berndt_galway_chunk_4678
import Theorems.Thm_Brocard_berndt_galway_chunk_4679
import Theorems.Thm_Brocard_berndt_galway_chunk_4680
import Theorems.Thm_Brocard_berndt_galway_chunk_4681
import Theorems.Thm_Brocard_berndt_galway_chunk_4682

theorem solution (n m : ℕ) (h1 : 833812949 ≤ n) (h2 : n < 842086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 837949640 with hs0 | hs0
  · -- n < 837949640
    rcases Nat.lt_or_ge n 835971223 with hs1 | hs1
    · -- n < 835971223
      rcases Nat.lt_or_ge n 834892086 with hs2 | hs2
      · -- n < 834892086
        rcases Nat.lt_or_ge n 834352517 with hs3 | hs3
        · -- n < 834352517
          rcases Nat.lt_or_ge n 834172661 with hs4 | hs4
          · -- n < 834172661
            rcases Nat.lt_or_ge n 833992805 with hs5 | hs5
            · -- n < 833992805
              exact Brocard.berndt_galway_chunk_4637 n m (by omega) (by omega) h
            · -- n >= 833992805
              exact Brocard.berndt_galway_chunk_4638 n m (by omega) (by omega) h
          · -- n >= 834172661
            exact Brocard.berndt_galway_chunk_4639 n m (by omega) (by omega) h
        · -- n >= 834352517
          rcases Nat.lt_or_ge n 834712230 with hs4 | hs4
          · -- n < 834712230
            rcases Nat.lt_or_ge n 834532374 with hs5 | hs5
            · -- n < 834532374
              exact Brocard.berndt_galway_chunk_4640 n m (by omega) (by omega) h
            · -- n >= 834532374
              exact Brocard.berndt_galway_chunk_4641 n m (by omega) (by omega) h
          · -- n >= 834712230
            exact Brocard.berndt_galway_chunk_4642 n m (by omega) (by omega) h
      · -- n >= 834892086
        rcases Nat.lt_or_ge n 835431654 with hs3 | hs3
        · -- n < 835431654
          rcases Nat.lt_or_ge n 835251798 with hs4 | hs4
          · -- n < 835251798
            rcases Nat.lt_or_ge n 835071942 with hs5 | hs5
            · -- n < 835071942
              exact Brocard.berndt_galway_chunk_4643 n m (by omega) (by omega) h
            · -- n >= 835071942
              exact Brocard.berndt_galway_chunk_4644 n m (by omega) (by omega) h
          · -- n >= 835251798
            exact Brocard.berndt_galway_chunk_4645 n m (by omega) (by omega) h
        · -- n >= 835431654
          rcases Nat.lt_or_ge n 835791366 with hs4 | hs4
          · -- n < 835791366
            rcases Nat.lt_or_ge n 835611510 with hs5 | hs5
            · -- n < 835611510
              exact Brocard.berndt_galway_chunk_4646 n m (by omega) (by omega) h
            · -- n >= 835611510
              exact Brocard.berndt_galway_chunk_4647 n m (by omega) (by omega) h
          · -- n >= 835791366
            exact Brocard.berndt_galway_chunk_4648 n m (by omega) (by omega) h
    · -- n >= 835971223
      rcases Nat.lt_or_ge n 837050359 with hs2 | hs2
      · -- n < 837050359
        rcases Nat.lt_or_ge n 836510791 with hs3 | hs3
        · -- n < 836510791
          rcases Nat.lt_or_ge n 836330935 with hs4 | hs4
          · -- n < 836330935
            rcases Nat.lt_or_ge n 836151079 with hs5 | hs5
            · -- n < 836151079
              exact Brocard.berndt_galway_chunk_4649 n m (by omega) (by omega) h
            · -- n >= 836151079
              exact Brocard.berndt_galway_chunk_4650 n m (by omega) (by omega) h
          · -- n >= 836330935
            exact Brocard.berndt_galway_chunk_4651 n m (by omega) (by omega) h
        · -- n >= 836510791
          rcases Nat.lt_or_ge n 836870503 with hs4 | hs4
          · -- n < 836870503
            rcases Nat.lt_or_ge n 836690647 with hs5 | hs5
            · -- n < 836690647
              exact Brocard.berndt_galway_chunk_4652 n m (by omega) (by omega) h
            · -- n >= 836690647
              exact Brocard.berndt_galway_chunk_4653 n m (by omega) (by omega) h
          · -- n >= 836870503
            exact Brocard.berndt_galway_chunk_4654 n m (by omega) (by omega) h
      · -- n >= 837050359
        rcases Nat.lt_or_ge n 837589928 with hs3 | hs3
        · -- n < 837589928
          rcases Nat.lt_or_ge n 837410071 with hs4 | hs4
          · -- n < 837410071
            rcases Nat.lt_or_ge n 837230215 with hs5 | hs5
            · -- n < 837230215
              exact Brocard.berndt_galway_chunk_4655 n m (by omega) (by omega) h
            · -- n >= 837230215
              exact Brocard.berndt_galway_chunk_4656 n m (by omega) (by omega) h
          · -- n >= 837410071
            exact Brocard.berndt_galway_chunk_4657 n m (by omega) (by omega) h
        · -- n >= 837589928
          rcases Nat.lt_or_ge n 837769784 with hs4 | hs4
          · -- n < 837769784
            exact Brocard.berndt_galway_chunk_4658 n m (by omega) (by omega) h
          · -- n >= 837769784
            exact Brocard.berndt_galway_chunk_4659 n m (by omega) (by omega) h
  · -- n >= 837949640
    rcases Nat.lt_or_ge n 840107913 with hs1 | hs1
    · -- n < 840107913
      rcases Nat.lt_or_ge n 839028776 with hs2 | hs2
      · -- n < 839028776
        rcases Nat.lt_or_ge n 838489208 with hs3 | hs3
        · -- n < 838489208
          rcases Nat.lt_or_ge n 838309352 with hs4 | hs4
          · -- n < 838309352
            rcases Nat.lt_or_ge n 838129496 with hs5 | hs5
            · -- n < 838129496
              exact Brocard.berndt_galway_chunk_4660 n m (by omega) (by omega) h
            · -- n >= 838129496
              exact Brocard.berndt_galway_chunk_4661 n m (by omega) (by omega) h
          · -- n >= 838309352
            exact Brocard.berndt_galway_chunk_4662 n m (by omega) (by omega) h
        · -- n >= 838489208
          rcases Nat.lt_or_ge n 838848920 with hs4 | hs4
          · -- n < 838848920
            rcases Nat.lt_or_ge n 838669064 with hs5 | hs5
            · -- n < 838669064
              exact Brocard.berndt_galway_chunk_4663 n m (by omega) (by omega) h
            · -- n >= 838669064
              exact Brocard.berndt_galway_chunk_4664 n m (by omega) (by omega) h
          · -- n >= 838848920
            exact Brocard.berndt_galway_chunk_4665 n m (by omega) (by omega) h
      · -- n >= 839028776
        rcases Nat.lt_or_ge n 839568345 with hs3 | hs3
        · -- n < 839568345
          rcases Nat.lt_or_ge n 839388489 with hs4 | hs4
          · -- n < 839388489
            rcases Nat.lt_or_ge n 839208633 with hs5 | hs5
            · -- n < 839208633
              exact Brocard.berndt_galway_chunk_4666 n m (by omega) (by omega) h
            · -- n >= 839208633
              exact Brocard.berndt_galway_chunk_4667 n m (by omega) (by omega) h
          · -- n >= 839388489
            exact Brocard.berndt_galway_chunk_4668 n m (by omega) (by omega) h
        · -- n >= 839568345
          rcases Nat.lt_or_ge n 839928057 with hs4 | hs4
          · -- n < 839928057
            rcases Nat.lt_or_ge n 839748201 with hs5 | hs5
            · -- n < 839748201
              exact Brocard.berndt_galway_chunk_4669 n m (by omega) (by omega) h
            · -- n >= 839748201
              exact Brocard.berndt_galway_chunk_4670 n m (by omega) (by omega) h
          · -- n >= 839928057
            exact Brocard.berndt_galway_chunk_4671 n m (by omega) (by omega) h
    · -- n >= 840107913
      rcases Nat.lt_or_ge n 841187050 with hs2 | hs2
      · -- n < 841187050
        rcases Nat.lt_or_ge n 840647482 with hs3 | hs3
        · -- n < 840647482
          rcases Nat.lt_or_ge n 840467625 with hs4 | hs4
          · -- n < 840467625
            rcases Nat.lt_or_ge n 840287769 with hs5 | hs5
            · -- n < 840287769
              exact Brocard.berndt_galway_chunk_4672 n m (by omega) (by omega) h
            · -- n >= 840287769
              exact Brocard.berndt_galway_chunk_4673 n m (by omega) (by omega) h
          · -- n >= 840467625
            exact Brocard.berndt_galway_chunk_4674 n m (by omega) (by omega) h
        · -- n >= 840647482
          rcases Nat.lt_or_ge n 841007194 with hs4 | hs4
          · -- n < 841007194
            rcases Nat.lt_or_ge n 840827338 with hs5 | hs5
            · -- n < 840827338
              exact Brocard.berndt_galway_chunk_4675 n m (by omega) (by omega) h
            · -- n >= 840827338
              exact Brocard.berndt_galway_chunk_4676 n m (by omega) (by omega) h
          · -- n >= 841007194
            exact Brocard.berndt_galway_chunk_4677 n m (by omega) (by omega) h
      · -- n >= 841187050
        rcases Nat.lt_or_ge n 841726618 with hs3 | hs3
        · -- n < 841726618
          rcases Nat.lt_or_ge n 841546762 with hs4 | hs4
          · -- n < 841546762
            rcases Nat.lt_or_ge n 841366906 with hs5 | hs5
            · -- n < 841366906
              exact Brocard.berndt_galway_chunk_4678 n m (by omega) (by omega) h
            · -- n >= 841366906
              exact Brocard.berndt_galway_chunk_4679 n m (by omega) (by omega) h
          · -- n >= 841546762
            exact Brocard.berndt_galway_chunk_4680 n m (by omega) (by omega) h
        · -- n >= 841726618
          rcases Nat.lt_or_ge n 841906474 with hs4 | hs4
          · -- n < 841906474
            exact Brocard.berndt_galway_chunk_4681 n m (by omega) (by omega) h
          · -- n >= 841906474
            exact Brocard.berndt_galway_chunk_4682 n m (by omega) (by omega) h
