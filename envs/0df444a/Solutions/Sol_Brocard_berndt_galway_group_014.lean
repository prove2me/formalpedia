-- Prove2me | solution 1 for Brocard.berndt_galway_group_014
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:06:59.32682+00:00
-- url     : https://prove2.me/submissions/9de9e616-994c-4fc1-8711-bd177fa784c1

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0604
import Theorems.Thm_Brocard_berndt_galway_chunk_0605
import Theorems.Thm_Brocard_berndt_galway_chunk_0606
import Theorems.Thm_Brocard_berndt_galway_chunk_0607
import Theorems.Thm_Brocard_berndt_galway_chunk_0608
import Theorems.Thm_Brocard_berndt_galway_chunk_0609
import Theorems.Thm_Brocard_berndt_galway_chunk_0610
import Theorems.Thm_Brocard_berndt_galway_chunk_0611
import Theorems.Thm_Brocard_berndt_galway_chunk_0612
import Theorems.Thm_Brocard_berndt_galway_chunk_0613
import Theorems.Thm_Brocard_berndt_galway_chunk_0614
import Theorems.Thm_Brocard_berndt_galway_chunk_0615
import Theorems.Thm_Brocard_berndt_galway_chunk_0616
import Theorems.Thm_Brocard_berndt_galway_chunk_0617
import Theorems.Thm_Brocard_berndt_galway_chunk_0618
import Theorems.Thm_Brocard_berndt_galway_chunk_0619
import Theorems.Thm_Brocard_berndt_galway_chunk_0620
import Theorems.Thm_Brocard_berndt_galway_chunk_0621
import Theorems.Thm_Brocard_berndt_galway_chunk_0622
import Theorems.Thm_Brocard_berndt_galway_chunk_0623
import Theorems.Thm_Brocard_berndt_galway_chunk_0624
import Theorems.Thm_Brocard_berndt_galway_chunk_0625
import Theorems.Thm_Brocard_berndt_galway_chunk_0626
import Theorems.Thm_Brocard_berndt_galway_chunk_0627
import Theorems.Thm_Brocard_berndt_galway_chunk_0628
import Theorems.Thm_Brocard_berndt_galway_chunk_0629
import Theorems.Thm_Brocard_berndt_galway_chunk_0630
import Theorems.Thm_Brocard_berndt_galway_chunk_0631
import Theorems.Thm_Brocard_berndt_galway_chunk_0632
import Theorems.Thm_Brocard_berndt_galway_chunk_0633
import Theorems.Thm_Brocard_berndt_galway_chunk_0634
import Theorems.Thm_Brocard_berndt_galway_chunk_0635
import Theorems.Thm_Brocard_berndt_galway_chunk_0636
import Theorems.Thm_Brocard_berndt_galway_chunk_0637
import Theorems.Thm_Brocard_berndt_galway_chunk_0638
import Theorems.Thm_Brocard_berndt_galway_chunk_0639
import Theorems.Thm_Brocard_berndt_galway_chunk_0640
import Theorems.Thm_Brocard_berndt_galway_chunk_0641
import Theorems.Thm_Brocard_berndt_galway_chunk_0642
import Theorems.Thm_Brocard_berndt_galway_chunk_0643
import Theorems.Thm_Brocard_berndt_galway_chunk_0644
import Theorems.Thm_Brocard_berndt_galway_chunk_0645
import Theorems.Thm_Brocard_berndt_galway_chunk_0646
import Theorems.Thm_Brocard_berndt_galway_chunk_0647
import Theorems.Thm_Brocard_berndt_galway_chunk_0648
import Theorems.Thm_Brocard_berndt_galway_chunk_0649
import Theorems.Thm_Brocard_berndt_galway_chunk_0650

theorem solution (n m : ℕ) (h1 : 108453237 ≤ n) (h2 : n < 116906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 112769784 with hs0 | hs0
  · -- n < 112769784
    rcases Nat.lt_or_ge n 110611510 with hs1 | hs1
    · -- n < 110611510
      rcases Nat.lt_or_ge n 109532374 with hs2 | hs2
      · -- n < 109532374
        rcases Nat.lt_or_ge n 108992805 with hs3 | hs3
        · -- n < 108992805
          rcases Nat.lt_or_ge n 108812949 with hs4 | hs4
          · -- n < 108812949
            rcases Nat.lt_or_ge n 108633093 with hs5 | hs5
            · -- n < 108633093
              exact Brocard.berndt_galway_chunk_0604 n m (by omega) (by omega) h
            · -- n >= 108633093
              exact Brocard.berndt_galway_chunk_0605 n m (by omega) (by omega) h
          · -- n >= 108812949
            exact Brocard.berndt_galway_chunk_0606 n m (by omega) (by omega) h
        · -- n >= 108992805
          rcases Nat.lt_or_ge n 109352517 with hs4 | hs4
          · -- n < 109352517
            rcases Nat.lt_or_ge n 109172661 with hs5 | hs5
            · -- n < 109172661
              exact Brocard.berndt_galway_chunk_0607 n m (by omega) (by omega) h
            · -- n >= 109172661
              exact Brocard.berndt_galway_chunk_0608 n m (by omega) (by omega) h
          · -- n >= 109352517
            exact Brocard.berndt_galway_chunk_0609 n m (by omega) (by omega) h
      · -- n >= 109532374
        rcases Nat.lt_or_ge n 110071942 with hs3 | hs3
        · -- n < 110071942
          rcases Nat.lt_or_ge n 109892086 with hs4 | hs4
          · -- n < 109892086
            rcases Nat.lt_or_ge n 109712230 with hs5 | hs5
            · -- n < 109712230
              exact Brocard.berndt_galway_chunk_0610 n m (by omega) (by omega) h
            · -- n >= 109712230
              exact Brocard.berndt_galway_chunk_0611 n m (by omega) (by omega) h
          · -- n >= 109892086
            exact Brocard.berndt_galway_chunk_0612 n m (by omega) (by omega) h
        · -- n >= 110071942
          rcases Nat.lt_or_ge n 110431654 with hs4 | hs4
          · -- n < 110431654
            rcases Nat.lt_or_ge n 110251798 with hs5 | hs5
            · -- n < 110251798
              exact Brocard.berndt_galway_chunk_0613 n m (by omega) (by omega) h
            · -- n >= 110251798
              exact Brocard.berndt_galway_chunk_0614 n m (by omega) (by omega) h
          · -- n >= 110431654
            exact Brocard.berndt_galway_chunk_0615 n m (by omega) (by omega) h
    · -- n >= 110611510
      rcases Nat.lt_or_ge n 111690647 with hs2 | hs2
      · -- n < 111690647
        rcases Nat.lt_or_ge n 111151079 with hs3 | hs3
        · -- n < 111151079
          rcases Nat.lt_or_ge n 110971223 with hs4 | hs4
          · -- n < 110971223
            rcases Nat.lt_or_ge n 110791366 with hs5 | hs5
            · -- n < 110791366
              exact Brocard.berndt_galway_chunk_0616 n m (by omega) (by omega) h
            · -- n >= 110791366
              exact Brocard.berndt_galway_chunk_0617 n m (by omega) (by omega) h
          · -- n >= 110971223
            exact Brocard.berndt_galway_chunk_0618 n m (by omega) (by omega) h
        · -- n >= 111151079
          rcases Nat.lt_or_ge n 111510791 with hs4 | hs4
          · -- n < 111510791
            rcases Nat.lt_or_ge n 111330935 with hs5 | hs5
            · -- n < 111330935
              exact Brocard.berndt_galway_chunk_0619 n m (by omega) (by omega) h
            · -- n >= 111330935
              exact Brocard.berndt_galway_chunk_0620 n m (by omega) (by omega) h
          · -- n >= 111510791
            exact Brocard.berndt_galway_chunk_0621 n m (by omega) (by omega) h
      · -- n >= 111690647
        rcases Nat.lt_or_ge n 112230215 with hs3 | hs3
        · -- n < 112230215
          rcases Nat.lt_or_ge n 112050359 with hs4 | hs4
          · -- n < 112050359
            rcases Nat.lt_or_ge n 111870503 with hs5 | hs5
            · -- n < 111870503
              exact Brocard.berndt_galway_chunk_0622 n m (by omega) (by omega) h
            · -- n >= 111870503
              exact Brocard.berndt_galway_chunk_0623 n m (by omega) (by omega) h
          · -- n >= 112050359
            exact Brocard.berndt_galway_chunk_0624 n m (by omega) (by omega) h
        · -- n >= 112230215
          rcases Nat.lt_or_ge n 112589928 with hs4 | hs4
          · -- n < 112589928
            rcases Nat.lt_or_ge n 112410071 with hs5 | hs5
            · -- n < 112410071
              exact Brocard.berndt_galway_chunk_0625 n m (by omega) (by omega) h
            · -- n >= 112410071
              exact Brocard.berndt_galway_chunk_0626 n m (by omega) (by omega) h
          · -- n >= 112589928
            exact Brocard.berndt_galway_chunk_0627 n m (by omega) (by omega) h
  · -- n >= 112769784
    rcases Nat.lt_or_ge n 114928057 with hs1 | hs1
    · -- n < 114928057
      rcases Nat.lt_or_ge n 113848920 with hs2 | hs2
      · -- n < 113848920
        rcases Nat.lt_or_ge n 113309352 with hs3 | hs3
        · -- n < 113309352
          rcases Nat.lt_or_ge n 113129496 with hs4 | hs4
          · -- n < 113129496
            rcases Nat.lt_or_ge n 112949640 with hs5 | hs5
            · -- n < 112949640
              exact Brocard.berndt_galway_chunk_0628 n m (by omega) (by omega) h
            · -- n >= 112949640
              exact Brocard.berndt_galway_chunk_0629 n m (by omega) (by omega) h
          · -- n >= 113129496
            exact Brocard.berndt_galway_chunk_0630 n m (by omega) (by omega) h
        · -- n >= 113309352
          rcases Nat.lt_or_ge n 113669064 with hs4 | hs4
          · -- n < 113669064
            rcases Nat.lt_or_ge n 113489208 with hs5 | hs5
            · -- n < 113489208
              exact Brocard.berndt_galway_chunk_0631 n m (by omega) (by omega) h
            · -- n >= 113489208
              exact Brocard.berndt_galway_chunk_0632 n m (by omega) (by omega) h
          · -- n >= 113669064
            exact Brocard.berndt_galway_chunk_0633 n m (by omega) (by omega) h
      · -- n >= 113848920
        rcases Nat.lt_or_ge n 114388489 with hs3 | hs3
        · -- n < 114388489
          rcases Nat.lt_or_ge n 114208633 with hs4 | hs4
          · -- n < 114208633
            rcases Nat.lt_or_ge n 114028776 with hs5 | hs5
            · -- n < 114028776
              exact Brocard.berndt_galway_chunk_0634 n m (by omega) (by omega) h
            · -- n >= 114028776
              exact Brocard.berndt_galway_chunk_0635 n m (by omega) (by omega) h
          · -- n >= 114208633
            exact Brocard.berndt_galway_chunk_0636 n m (by omega) (by omega) h
        · -- n >= 114388489
          rcases Nat.lt_or_ge n 114748201 with hs4 | hs4
          · -- n < 114748201
            rcases Nat.lt_or_ge n 114568345 with hs5 | hs5
            · -- n < 114568345
              exact Brocard.berndt_galway_chunk_0637 n m (by omega) (by omega) h
            · -- n >= 114568345
              exact Brocard.berndt_galway_chunk_0638 n m (by omega) (by omega) h
          · -- n >= 114748201
            exact Brocard.berndt_galway_chunk_0639 n m (by omega) (by omega) h
    · -- n >= 114928057
      rcases Nat.lt_or_ge n 116007194 with hs2 | hs2
      · -- n < 116007194
        rcases Nat.lt_or_ge n 115467625 with hs3 | hs3
        · -- n < 115467625
          rcases Nat.lt_or_ge n 115287769 with hs4 | hs4
          · -- n < 115287769
            rcases Nat.lt_or_ge n 115107913 with hs5 | hs5
            · -- n < 115107913
              exact Brocard.berndt_galway_chunk_0640 n m (by omega) (by omega) h
            · -- n >= 115107913
              exact Brocard.berndt_galway_chunk_0641 n m (by omega) (by omega) h
          · -- n >= 115287769
            exact Brocard.berndt_galway_chunk_0642 n m (by omega) (by omega) h
        · -- n >= 115467625
          rcases Nat.lt_or_ge n 115827338 with hs4 | hs4
          · -- n < 115827338
            rcases Nat.lt_or_ge n 115647482 with hs5 | hs5
            · -- n < 115647482
              exact Brocard.berndt_galway_chunk_0643 n m (by omega) (by omega) h
            · -- n >= 115647482
              exact Brocard.berndt_galway_chunk_0644 n m (by omega) (by omega) h
          · -- n >= 115827338
            exact Brocard.berndt_galway_chunk_0645 n m (by omega) (by omega) h
      · -- n >= 116007194
        rcases Nat.lt_or_ge n 116546762 with hs3 | hs3
        · -- n < 116546762
          rcases Nat.lt_or_ge n 116366906 with hs4 | hs4
          · -- n < 116366906
            rcases Nat.lt_or_ge n 116187050 with hs5 | hs5
            · -- n < 116187050
              exact Brocard.berndt_galway_chunk_0646 n m (by omega) (by omega) h
            · -- n >= 116187050
              exact Brocard.berndt_galway_chunk_0647 n m (by omega) (by omega) h
          · -- n >= 116366906
            exact Brocard.berndt_galway_chunk_0648 n m (by omega) (by omega) h
        · -- n >= 116546762
          rcases Nat.lt_or_ge n 116726618 with hs4 | hs4
          · -- n < 116726618
            exact Brocard.berndt_galway_chunk_0649 n m (by omega) (by omega) h
          · -- n >= 116726618
            exact Brocard.berndt_galway_chunk_0650 n m (by omega) (by omega) h
