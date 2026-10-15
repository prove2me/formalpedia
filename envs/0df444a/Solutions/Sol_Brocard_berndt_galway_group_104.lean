-- Prove2me | solution 1 for Brocard.berndt_galway_group_104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:56:17.126775+00:00
-- url     : https://prove2.me/submissions/0ce1afdc-e926-4fac-83c9-50ddd98183c1

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4775
import Theorems.Thm_Brocard_berndt_galway_chunk_4776
import Theorems.Thm_Brocard_berndt_galway_chunk_4777
import Theorems.Thm_Brocard_berndt_galway_chunk_4778
import Theorems.Thm_Brocard_berndt_galway_chunk_4779
import Theorems.Thm_Brocard_berndt_galway_chunk_4780
import Theorems.Thm_Brocard_berndt_galway_chunk_4781
import Theorems.Thm_Brocard_berndt_galway_chunk_4782
import Theorems.Thm_Brocard_berndt_galway_chunk_4783
import Theorems.Thm_Brocard_berndt_galway_chunk_4784
import Theorems.Thm_Brocard_berndt_galway_chunk_4785
import Theorems.Thm_Brocard_berndt_galway_chunk_4786
import Theorems.Thm_Brocard_berndt_galway_chunk_4787
import Theorems.Thm_Brocard_berndt_galway_chunk_4788
import Theorems.Thm_Brocard_berndt_galway_chunk_4789
import Theorems.Thm_Brocard_berndt_galway_chunk_4790
import Theorems.Thm_Brocard_berndt_galway_chunk_4791
import Theorems.Thm_Brocard_berndt_galway_chunk_4792
import Theorems.Thm_Brocard_berndt_galway_chunk_4793
import Theorems.Thm_Brocard_berndt_galway_chunk_4794
import Theorems.Thm_Brocard_berndt_galway_chunk_4795
import Theorems.Thm_Brocard_berndt_galway_chunk_4796
import Theorems.Thm_Brocard_berndt_galway_chunk_4797
import Theorems.Thm_Brocard_berndt_galway_chunk_4798
import Theorems.Thm_Brocard_berndt_galway_chunk_4799
import Theorems.Thm_Brocard_berndt_galway_chunk_4800
import Theorems.Thm_Brocard_berndt_galway_chunk_4801
import Theorems.Thm_Brocard_berndt_galway_chunk_4802
import Theorems.Thm_Brocard_berndt_galway_chunk_4803
import Theorems.Thm_Brocard_berndt_galway_chunk_4804
import Theorems.Thm_Brocard_berndt_galway_chunk_4805
import Theorems.Thm_Brocard_berndt_galway_chunk_4806
import Theorems.Thm_Brocard_berndt_galway_chunk_4807
import Theorems.Thm_Brocard_berndt_galway_chunk_4808
import Theorems.Thm_Brocard_berndt_galway_chunk_4809
import Theorems.Thm_Brocard_berndt_galway_chunk_4810
import Theorems.Thm_Brocard_berndt_galway_chunk_4811
import Theorems.Thm_Brocard_berndt_galway_chunk_4812
import Theorems.Thm_Brocard_berndt_galway_chunk_4813
import Theorems.Thm_Brocard_berndt_galway_chunk_4814
import Theorems.Thm_Brocard_berndt_galway_chunk_4815
import Theorems.Thm_Brocard_berndt_galway_chunk_4816
import Theorems.Thm_Brocard_berndt_galway_chunk_4817
import Theorems.Thm_Brocard_berndt_galway_chunk_4818
import Theorems.Thm_Brocard_berndt_galway_chunk_4819
import Theorems.Thm_Brocard_berndt_galway_chunk_4820

theorem solution (n m : ℕ) (h1 : 858633093 ≤ n) (h2 : n < 866906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 862769784 with hs0 | hs0
  · -- n < 862769784
    rcases Nat.lt_or_ge n 860791366 with hs1 | hs1
    · -- n < 860791366
      rcases Nat.lt_or_ge n 859712230 with hs2 | hs2
      · -- n < 859712230
        rcases Nat.lt_or_ge n 859172661 with hs3 | hs3
        · -- n < 859172661
          rcases Nat.lt_or_ge n 858992805 with hs4 | hs4
          · -- n < 858992805
            rcases Nat.lt_or_ge n 858812949 with hs5 | hs5
            · -- n < 858812949
              exact Brocard.berndt_galway_chunk_4775 n m (by omega) (by omega) h
            · -- n >= 858812949
              exact Brocard.berndt_galway_chunk_4776 n m (by omega) (by omega) h
          · -- n >= 858992805
            exact Brocard.berndt_galway_chunk_4777 n m (by omega) (by omega) h
        · -- n >= 859172661
          rcases Nat.lt_or_ge n 859532374 with hs4 | hs4
          · -- n < 859532374
            rcases Nat.lt_or_ge n 859352517 with hs5 | hs5
            · -- n < 859352517
              exact Brocard.berndt_galway_chunk_4778 n m (by omega) (by omega) h
            · -- n >= 859352517
              exact Brocard.berndt_galway_chunk_4779 n m (by omega) (by omega) h
          · -- n >= 859532374
            exact Brocard.berndt_galway_chunk_4780 n m (by omega) (by omega) h
      · -- n >= 859712230
        rcases Nat.lt_or_ge n 860251798 with hs3 | hs3
        · -- n < 860251798
          rcases Nat.lt_or_ge n 860071942 with hs4 | hs4
          · -- n < 860071942
            rcases Nat.lt_or_ge n 859892086 with hs5 | hs5
            · -- n < 859892086
              exact Brocard.berndt_galway_chunk_4781 n m (by omega) (by omega) h
            · -- n >= 859892086
              exact Brocard.berndt_galway_chunk_4782 n m (by omega) (by omega) h
          · -- n >= 860071942
            exact Brocard.berndt_galway_chunk_4783 n m (by omega) (by omega) h
        · -- n >= 860251798
          rcases Nat.lt_or_ge n 860611510 with hs4 | hs4
          · -- n < 860611510
            rcases Nat.lt_or_ge n 860431654 with hs5 | hs5
            · -- n < 860431654
              exact Brocard.berndt_galway_chunk_4784 n m (by omega) (by omega) h
            · -- n >= 860431654
              exact Brocard.berndt_galway_chunk_4785 n m (by omega) (by omega) h
          · -- n >= 860611510
            exact Brocard.berndt_galway_chunk_4786 n m (by omega) (by omega) h
    · -- n >= 860791366
      rcases Nat.lt_or_ge n 861870503 with hs2 | hs2
      · -- n < 861870503
        rcases Nat.lt_or_ge n 861330935 with hs3 | hs3
        · -- n < 861330935
          rcases Nat.lt_or_ge n 861151079 with hs4 | hs4
          · -- n < 861151079
            rcases Nat.lt_or_ge n 860971223 with hs5 | hs5
            · -- n < 860971223
              exact Brocard.berndt_galway_chunk_4787 n m (by omega) (by omega) h
            · -- n >= 860971223
              exact Brocard.berndt_galway_chunk_4788 n m (by omega) (by omega) h
          · -- n >= 861151079
            exact Brocard.berndt_galway_chunk_4789 n m (by omega) (by omega) h
        · -- n >= 861330935
          rcases Nat.lt_or_ge n 861690647 with hs4 | hs4
          · -- n < 861690647
            rcases Nat.lt_or_ge n 861510791 with hs5 | hs5
            · -- n < 861510791
              exact Brocard.berndt_galway_chunk_4790 n m (by omega) (by omega) h
            · -- n >= 861510791
              exact Brocard.berndt_galway_chunk_4791 n m (by omega) (by omega) h
          · -- n >= 861690647
            exact Brocard.berndt_galway_chunk_4792 n m (by omega) (by omega) h
      · -- n >= 861870503
        rcases Nat.lt_or_ge n 862410071 with hs3 | hs3
        · -- n < 862410071
          rcases Nat.lt_or_ge n 862230215 with hs4 | hs4
          · -- n < 862230215
            rcases Nat.lt_or_ge n 862050359 with hs5 | hs5
            · -- n < 862050359
              exact Brocard.berndt_galway_chunk_4793 n m (by omega) (by omega) h
            · -- n >= 862050359
              exact Brocard.berndt_galway_chunk_4794 n m (by omega) (by omega) h
          · -- n >= 862230215
            exact Brocard.berndt_galway_chunk_4795 n m (by omega) (by omega) h
        · -- n >= 862410071
          rcases Nat.lt_or_ge n 862589928 with hs4 | hs4
          · -- n < 862589928
            exact Brocard.berndt_galway_chunk_4796 n m (by omega) (by omega) h
          · -- n >= 862589928
            exact Brocard.berndt_galway_chunk_4797 n m (by omega) (by omega) h
  · -- n >= 862769784
    rcases Nat.lt_or_ge n 864928057 with hs1 | hs1
    · -- n < 864928057
      rcases Nat.lt_or_ge n 863848920 with hs2 | hs2
      · -- n < 863848920
        rcases Nat.lt_or_ge n 863309352 with hs3 | hs3
        · -- n < 863309352
          rcases Nat.lt_or_ge n 863129496 with hs4 | hs4
          · -- n < 863129496
            rcases Nat.lt_or_ge n 862949640 with hs5 | hs5
            · -- n < 862949640
              exact Brocard.berndt_galway_chunk_4798 n m (by omega) (by omega) h
            · -- n >= 862949640
              exact Brocard.berndt_galway_chunk_4799 n m (by omega) (by omega) h
          · -- n >= 863129496
            exact Brocard.berndt_galway_chunk_4800 n m (by omega) (by omega) h
        · -- n >= 863309352
          rcases Nat.lt_or_ge n 863669064 with hs4 | hs4
          · -- n < 863669064
            rcases Nat.lt_or_ge n 863489208 with hs5 | hs5
            · -- n < 863489208
              exact Brocard.berndt_galway_chunk_4801 n m (by omega) (by omega) h
            · -- n >= 863489208
              exact Brocard.berndt_galway_chunk_4802 n m (by omega) (by omega) h
          · -- n >= 863669064
            exact Brocard.berndt_galway_chunk_4803 n m (by omega) (by omega) h
      · -- n >= 863848920
        rcases Nat.lt_or_ge n 864388489 with hs3 | hs3
        · -- n < 864388489
          rcases Nat.lt_or_ge n 864208633 with hs4 | hs4
          · -- n < 864208633
            rcases Nat.lt_or_ge n 864028776 with hs5 | hs5
            · -- n < 864028776
              exact Brocard.berndt_galway_chunk_4804 n m (by omega) (by omega) h
            · -- n >= 864028776
              exact Brocard.berndt_galway_chunk_4805 n m (by omega) (by omega) h
          · -- n >= 864208633
            exact Brocard.berndt_galway_chunk_4806 n m (by omega) (by omega) h
        · -- n >= 864388489
          rcases Nat.lt_or_ge n 864748201 with hs4 | hs4
          · -- n < 864748201
            rcases Nat.lt_or_ge n 864568345 with hs5 | hs5
            · -- n < 864568345
              exact Brocard.berndt_galway_chunk_4807 n m (by omega) (by omega) h
            · -- n >= 864568345
              exact Brocard.berndt_galway_chunk_4808 n m (by omega) (by omega) h
          · -- n >= 864748201
            exact Brocard.berndt_galway_chunk_4809 n m (by omega) (by omega) h
    · -- n >= 864928057
      rcases Nat.lt_or_ge n 866007194 with hs2 | hs2
      · -- n < 866007194
        rcases Nat.lt_or_ge n 865467625 with hs3 | hs3
        · -- n < 865467625
          rcases Nat.lt_or_ge n 865287769 with hs4 | hs4
          · -- n < 865287769
            rcases Nat.lt_or_ge n 865107913 with hs5 | hs5
            · -- n < 865107913
              exact Brocard.berndt_galway_chunk_4810 n m (by omega) (by omega) h
            · -- n >= 865107913
              exact Brocard.berndt_galway_chunk_4811 n m (by omega) (by omega) h
          · -- n >= 865287769
            exact Brocard.berndt_galway_chunk_4812 n m (by omega) (by omega) h
        · -- n >= 865467625
          rcases Nat.lt_or_ge n 865827338 with hs4 | hs4
          · -- n < 865827338
            rcases Nat.lt_or_ge n 865647482 with hs5 | hs5
            · -- n < 865647482
              exact Brocard.berndt_galway_chunk_4813 n m (by omega) (by omega) h
            · -- n >= 865647482
              exact Brocard.berndt_galway_chunk_4814 n m (by omega) (by omega) h
          · -- n >= 865827338
            exact Brocard.berndt_galway_chunk_4815 n m (by omega) (by omega) h
      · -- n >= 866007194
        rcases Nat.lt_or_ge n 866546762 with hs3 | hs3
        · -- n < 866546762
          rcases Nat.lt_or_ge n 866366906 with hs4 | hs4
          · -- n < 866366906
            rcases Nat.lt_or_ge n 866187050 with hs5 | hs5
            · -- n < 866187050
              exact Brocard.berndt_galway_chunk_4816 n m (by omega) (by omega) h
            · -- n >= 866187050
              exact Brocard.berndt_galway_chunk_4817 n m (by omega) (by omega) h
          · -- n >= 866366906
            exact Brocard.berndt_galway_chunk_4818 n m (by omega) (by omega) h
        · -- n >= 866546762
          rcases Nat.lt_or_ge n 866726618 with hs4 | hs4
          · -- n < 866726618
            exact Brocard.berndt_galway_chunk_4819 n m (by omega) (by omega) h
          · -- n >= 866726618
            exact Brocard.berndt_galway_chunk_4820 n m (by omega) (by omega) h
