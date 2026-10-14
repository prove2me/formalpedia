-- Prove2me | solution 1 for Brocard.berndt_galway_group_016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:38:24.319544+00:00
-- url     : https://prove2.me/submissions/bd0eb3f8-9af6-40de-81d9-0570961b35cc

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0698
import Theorems.Thm_Brocard_berndt_galway_chunk_0699
import Theorems.Thm_Brocard_berndt_galway_chunk_0700
import Theorems.Thm_Brocard_berndt_galway_chunk_0701
import Theorems.Thm_Brocard_berndt_galway_chunk_0702
import Theorems.Thm_Brocard_berndt_galway_chunk_0703
import Theorems.Thm_Brocard_berndt_galway_chunk_0704
import Theorems.Thm_Brocard_berndt_galway_chunk_0705
import Theorems.Thm_Brocard_berndt_galway_chunk_0706
import Theorems.Thm_Brocard_berndt_galway_chunk_0707
import Theorems.Thm_Brocard_berndt_galway_chunk_0708
import Theorems.Thm_Brocard_berndt_galway_chunk_0709
import Theorems.Thm_Brocard_berndt_galway_chunk_0710
import Theorems.Thm_Brocard_berndt_galway_chunk_0711
import Theorems.Thm_Brocard_berndt_galway_chunk_0712
import Theorems.Thm_Brocard_berndt_galway_chunk_0713
import Theorems.Thm_Brocard_berndt_galway_chunk_0714
import Theorems.Thm_Brocard_berndt_galway_chunk_0715
import Theorems.Thm_Brocard_berndt_galway_chunk_0716
import Theorems.Thm_Brocard_berndt_galway_chunk_0717
import Theorems.Thm_Brocard_berndt_galway_chunk_0718
import Theorems.Thm_Brocard_berndt_galway_chunk_0719
import Theorems.Thm_Brocard_berndt_galway_chunk_0720
import Theorems.Thm_Brocard_berndt_galway_chunk_0721
import Theorems.Thm_Brocard_berndt_galway_chunk_0722
import Theorems.Thm_Brocard_berndt_galway_chunk_0723
import Theorems.Thm_Brocard_berndt_galway_chunk_0724
import Theorems.Thm_Brocard_berndt_galway_chunk_0725
import Theorems.Thm_Brocard_berndt_galway_chunk_0726
import Theorems.Thm_Brocard_berndt_galway_chunk_0727
import Theorems.Thm_Brocard_berndt_galway_chunk_0728
import Theorems.Thm_Brocard_berndt_galway_chunk_0729
import Theorems.Thm_Brocard_berndt_galway_chunk_0730
import Theorems.Thm_Brocard_berndt_galway_chunk_0731
import Theorems.Thm_Brocard_berndt_galway_chunk_0732
import Theorems.Thm_Brocard_berndt_galway_chunk_0733
import Theorems.Thm_Brocard_berndt_galway_chunk_0734
import Theorems.Thm_Brocard_berndt_galway_chunk_0735
import Theorems.Thm_Brocard_berndt_galway_chunk_0736
import Theorems.Thm_Brocard_berndt_galway_chunk_0737
import Theorems.Thm_Brocard_berndt_galway_chunk_0738
import Theorems.Thm_Brocard_berndt_galway_chunk_0739
import Theorems.Thm_Brocard_berndt_galway_chunk_0740
import Theorems.Thm_Brocard_berndt_galway_chunk_0741
import Theorems.Thm_Brocard_berndt_galway_chunk_0742
import Theorems.Thm_Brocard_berndt_galway_chunk_0743
import Theorems.Thm_Brocard_berndt_galway_chunk_0744

theorem solution (n m : ℕ) (h1 : 125359712 ≤ n) (h2 : n < 133812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 129676258 with hs0 | hs0
  · -- n < 129676258
    rcases Nat.lt_or_ge n 127517985 with hs1 | hs1
    · -- n < 127517985
      rcases Nat.lt_or_ge n 126438848 with hs2 | hs2
      · -- n < 126438848
        rcases Nat.lt_or_ge n 125899280 with hs3 | hs3
        · -- n < 125899280
          rcases Nat.lt_or_ge n 125719424 with hs4 | hs4
          · -- n < 125719424
            rcases Nat.lt_or_ge n 125539568 with hs5 | hs5
            · -- n < 125539568
              exact Brocard.berndt_galway_chunk_0698 n m (by omega) (by omega) h
            · -- n >= 125539568
              exact Brocard.berndt_galway_chunk_0699 n m (by omega) (by omega) h
          · -- n >= 125719424
            exact Brocard.berndt_galway_chunk_0700 n m (by omega) (by omega) h
        · -- n >= 125899280
          rcases Nat.lt_or_ge n 126258992 with hs4 | hs4
          · -- n < 126258992
            rcases Nat.lt_or_ge n 126079136 with hs5 | hs5
            · -- n < 126079136
              exact Brocard.berndt_galway_chunk_0701 n m (by omega) (by omega) h
            · -- n >= 126079136
              exact Brocard.berndt_galway_chunk_0702 n m (by omega) (by omega) h
          · -- n >= 126258992
            exact Brocard.berndt_galway_chunk_0703 n m (by omega) (by omega) h
      · -- n >= 126438848
        rcases Nat.lt_or_ge n 126978417 with hs3 | hs3
        · -- n < 126978417
          rcases Nat.lt_or_ge n 126798561 with hs4 | hs4
          · -- n < 126798561
            rcases Nat.lt_or_ge n 126618705 with hs5 | hs5
            · -- n < 126618705
              exact Brocard.berndt_galway_chunk_0704 n m (by omega) (by omega) h
            · -- n >= 126618705
              exact Brocard.berndt_galway_chunk_0705 n m (by omega) (by omega) h
          · -- n >= 126798561
            exact Brocard.berndt_galway_chunk_0706 n m (by omega) (by omega) h
        · -- n >= 126978417
          rcases Nat.lt_or_ge n 127338129 with hs4 | hs4
          · -- n < 127338129
            rcases Nat.lt_or_ge n 127158273 with hs5 | hs5
            · -- n < 127158273
              exact Brocard.berndt_galway_chunk_0707 n m (by omega) (by omega) h
            · -- n >= 127158273
              exact Brocard.berndt_galway_chunk_0708 n m (by omega) (by omega) h
          · -- n >= 127338129
            exact Brocard.berndt_galway_chunk_0709 n m (by omega) (by omega) h
    · -- n >= 127517985
      rcases Nat.lt_or_ge n 128597122 with hs2 | hs2
      · -- n < 128597122
        rcases Nat.lt_or_ge n 128057553 with hs3 | hs3
        · -- n < 128057553
          rcases Nat.lt_or_ge n 127877697 with hs4 | hs4
          · -- n < 127877697
            rcases Nat.lt_or_ge n 127697841 with hs5 | hs5
            · -- n < 127697841
              exact Brocard.berndt_galway_chunk_0710 n m (by omega) (by omega) h
            · -- n >= 127697841
              exact Brocard.berndt_galway_chunk_0711 n m (by omega) (by omega) h
          · -- n >= 127877697
            exact Brocard.berndt_galway_chunk_0712 n m (by omega) (by omega) h
        · -- n >= 128057553
          rcases Nat.lt_or_ge n 128417266 with hs4 | hs4
          · -- n < 128417266
            rcases Nat.lt_or_ge n 128237410 with hs5 | hs5
            · -- n < 128237410
              exact Brocard.berndt_galway_chunk_0713 n m (by omega) (by omega) h
            · -- n >= 128237410
              exact Brocard.berndt_galway_chunk_0714 n m (by omega) (by omega) h
          · -- n >= 128417266
            exact Brocard.berndt_galway_chunk_0715 n m (by omega) (by omega) h
      · -- n >= 128597122
        rcases Nat.lt_or_ge n 129136690 with hs3 | hs3
        · -- n < 129136690
          rcases Nat.lt_or_ge n 128956834 with hs4 | hs4
          · -- n < 128956834
            rcases Nat.lt_or_ge n 128776978 with hs5 | hs5
            · -- n < 128776978
              exact Brocard.berndt_galway_chunk_0716 n m (by omega) (by omega) h
            · -- n >= 128776978
              exact Brocard.berndt_galway_chunk_0717 n m (by omega) (by omega) h
          · -- n >= 128956834
            exact Brocard.berndt_galway_chunk_0718 n m (by omega) (by omega) h
        · -- n >= 129136690
          rcases Nat.lt_or_ge n 129496402 with hs4 | hs4
          · -- n < 129496402
            rcases Nat.lt_or_ge n 129316546 with hs5 | hs5
            · -- n < 129316546
              exact Brocard.berndt_galway_chunk_0719 n m (by omega) (by omega) h
            · -- n >= 129316546
              exact Brocard.berndt_galway_chunk_0720 n m (by omega) (by omega) h
          · -- n >= 129496402
            exact Brocard.berndt_galway_chunk_0721 n m (by omega) (by omega) h
  · -- n >= 129676258
    rcases Nat.lt_or_ge n 131834532 with hs1 | hs1
    · -- n < 131834532
      rcases Nat.lt_or_ge n 130755395 with hs2 | hs2
      · -- n < 130755395
        rcases Nat.lt_or_ge n 130215827 with hs3 | hs3
        · -- n < 130215827
          rcases Nat.lt_or_ge n 130035971 with hs4 | hs4
          · -- n < 130035971
            rcases Nat.lt_or_ge n 129856115 with hs5 | hs5
            · -- n < 129856115
              exact Brocard.berndt_galway_chunk_0722 n m (by omega) (by omega) h
            · -- n >= 129856115
              exact Brocard.berndt_galway_chunk_0723 n m (by omega) (by omega) h
          · -- n >= 130035971
            exact Brocard.berndt_galway_chunk_0724 n m (by omega) (by omega) h
        · -- n >= 130215827
          rcases Nat.lt_or_ge n 130575539 with hs4 | hs4
          · -- n < 130575539
            rcases Nat.lt_or_ge n 130395683 with hs5 | hs5
            · -- n < 130395683
              exact Brocard.berndt_galway_chunk_0725 n m (by omega) (by omega) h
            · -- n >= 130395683
              exact Brocard.berndt_galway_chunk_0726 n m (by omega) (by omega) h
          · -- n >= 130575539
            exact Brocard.berndt_galway_chunk_0727 n m (by omega) (by omega) h
      · -- n >= 130755395
        rcases Nat.lt_or_ge n 131294964 with hs3 | hs3
        · -- n < 131294964
          rcases Nat.lt_or_ge n 131115107 with hs4 | hs4
          · -- n < 131115107
            rcases Nat.lt_or_ge n 130935251 with hs5 | hs5
            · -- n < 130935251
              exact Brocard.berndt_galway_chunk_0728 n m (by omega) (by omega) h
            · -- n >= 130935251
              exact Brocard.berndt_galway_chunk_0729 n m (by omega) (by omega) h
          · -- n >= 131115107
            exact Brocard.berndt_galway_chunk_0730 n m (by omega) (by omega) h
        · -- n >= 131294964
          rcases Nat.lt_or_ge n 131654676 with hs4 | hs4
          · -- n < 131654676
            rcases Nat.lt_or_ge n 131474820 with hs5 | hs5
            · -- n < 131474820
              exact Brocard.berndt_galway_chunk_0731 n m (by omega) (by omega) h
            · -- n >= 131474820
              exact Brocard.berndt_galway_chunk_0732 n m (by omega) (by omega) h
          · -- n >= 131654676
            exact Brocard.berndt_galway_chunk_0733 n m (by omega) (by omega) h
    · -- n >= 131834532
      rcases Nat.lt_or_ge n 132913669 with hs2 | hs2
      · -- n < 132913669
        rcases Nat.lt_or_ge n 132374100 with hs3 | hs3
        · -- n < 132374100
          rcases Nat.lt_or_ge n 132194244 with hs4 | hs4
          · -- n < 132194244
            rcases Nat.lt_or_ge n 132014388 with hs5 | hs5
            · -- n < 132014388
              exact Brocard.berndt_galway_chunk_0734 n m (by omega) (by omega) h
            · -- n >= 132014388
              exact Brocard.berndt_galway_chunk_0735 n m (by omega) (by omega) h
          · -- n >= 132194244
            exact Brocard.berndt_galway_chunk_0736 n m (by omega) (by omega) h
        · -- n >= 132374100
          rcases Nat.lt_or_ge n 132733812 with hs4 | hs4
          · -- n < 132733812
            rcases Nat.lt_or_ge n 132553956 with hs5 | hs5
            · -- n < 132553956
              exact Brocard.berndt_galway_chunk_0737 n m (by omega) (by omega) h
            · -- n >= 132553956
              exact Brocard.berndt_galway_chunk_0738 n m (by omega) (by omega) h
          · -- n >= 132733812
            exact Brocard.berndt_galway_chunk_0739 n m (by omega) (by omega) h
      · -- n >= 132913669
        rcases Nat.lt_or_ge n 133453237 with hs3 | hs3
        · -- n < 133453237
          rcases Nat.lt_or_ge n 133273381 with hs4 | hs4
          · -- n < 133273381
            rcases Nat.lt_or_ge n 133093525 with hs5 | hs5
            · -- n < 133093525
              exact Brocard.berndt_galway_chunk_0740 n m (by omega) (by omega) h
            · -- n >= 133093525
              exact Brocard.berndt_galway_chunk_0741 n m (by omega) (by omega) h
          · -- n >= 133273381
            exact Brocard.berndt_galway_chunk_0742 n m (by omega) (by omega) h
        · -- n >= 133453237
          rcases Nat.lt_or_ge n 133633093 with hs4 | hs4
          · -- n < 133633093
            exact Brocard.berndt_galway_chunk_0743 n m (by omega) (by omega) h
          · -- n >= 133633093
            exact Brocard.berndt_galway_chunk_0744 n m (by omega) (by omega) h
