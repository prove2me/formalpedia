-- Prove2me | solution 1 for Brocard.berndt_galway_group_062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:06:16.734971+00:00
-- url     : https://prove2.me/submissions/236a9ba8-759b-44ec-9cb5-1592641c8625

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2828
import Theorems.Thm_Brocard_berndt_galway_chunk_2829
import Theorems.Thm_Brocard_berndt_galway_chunk_2830
import Theorems.Thm_Brocard_berndt_galway_chunk_2831
import Theorems.Thm_Brocard_berndt_galway_chunk_2832
import Theorems.Thm_Brocard_berndt_galway_chunk_2833
import Theorems.Thm_Brocard_berndt_galway_chunk_2834
import Theorems.Thm_Brocard_berndt_galway_chunk_2835
import Theorems.Thm_Brocard_berndt_galway_chunk_2836
import Theorems.Thm_Brocard_berndt_galway_chunk_2837
import Theorems.Thm_Brocard_berndt_galway_chunk_2838
import Theorems.Thm_Brocard_berndt_galway_chunk_2839
import Theorems.Thm_Brocard_berndt_galway_chunk_2840
import Theorems.Thm_Brocard_berndt_galway_chunk_2841
import Theorems.Thm_Brocard_berndt_galway_chunk_2842
import Theorems.Thm_Brocard_berndt_galway_chunk_2843
import Theorems.Thm_Brocard_berndt_galway_chunk_2844
import Theorems.Thm_Brocard_berndt_galway_chunk_2845
import Theorems.Thm_Brocard_berndt_galway_chunk_2846
import Theorems.Thm_Brocard_berndt_galway_chunk_2847
import Theorems.Thm_Brocard_berndt_galway_chunk_2848
import Theorems.Thm_Brocard_berndt_galway_chunk_2849
import Theorems.Thm_Brocard_berndt_galway_chunk_2850
import Theorems.Thm_Brocard_berndt_galway_chunk_2851
import Theorems.Thm_Brocard_berndt_galway_chunk_2852
import Theorems.Thm_Brocard_berndt_galway_chunk_2853
import Theorems.Thm_Brocard_berndt_galway_chunk_2854
import Theorems.Thm_Brocard_berndt_galway_chunk_2855
import Theorems.Thm_Brocard_berndt_galway_chunk_2856
import Theorems.Thm_Brocard_berndt_galway_chunk_2857
import Theorems.Thm_Brocard_berndt_galway_chunk_2858
import Theorems.Thm_Brocard_berndt_galway_chunk_2859
import Theorems.Thm_Brocard_berndt_galway_chunk_2860
import Theorems.Thm_Brocard_berndt_galway_chunk_2861
import Theorems.Thm_Brocard_berndt_galway_chunk_2862
import Theorems.Thm_Brocard_berndt_galway_chunk_2863
import Theorems.Thm_Brocard_berndt_galway_chunk_2864
import Theorems.Thm_Brocard_berndt_galway_chunk_2865
import Theorems.Thm_Brocard_berndt_galway_chunk_2866
import Theorems.Thm_Brocard_berndt_galway_chunk_2867
import Theorems.Thm_Brocard_berndt_galway_chunk_2868
import Theorems.Thm_Brocard_berndt_galway_chunk_2869
import Theorems.Thm_Brocard_berndt_galway_chunk_2870
import Theorems.Thm_Brocard_berndt_galway_chunk_2871
import Theorems.Thm_Brocard_berndt_galway_chunk_2872
import Theorems.Thm_Brocard_berndt_galway_chunk_2873
import Theorems.Thm_Brocard_berndt_galway_chunk_2874

theorem solution (n m : ℕ) (h1 : 508453237 ≤ n) (h2 : n < 516906474) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 512769784 with hs0 | hs0
  · -- n < 512769784
    rcases Nat.lt_or_ge n 510611510 with hs1 | hs1
    · -- n < 510611510
      rcases Nat.lt_or_ge n 509532374 with hs2 | hs2
      · -- n < 509532374
        rcases Nat.lt_or_ge n 508992805 with hs3 | hs3
        · -- n < 508992805
          rcases Nat.lt_or_ge n 508812949 with hs4 | hs4
          · -- n < 508812949
            rcases Nat.lt_or_ge n 508633093 with hs5 | hs5
            · -- n < 508633093
              exact Brocard.berndt_galway_chunk_2828 n m (by omega) (by omega) h
            · -- n >= 508633093
              exact Brocard.berndt_galway_chunk_2829 n m (by omega) (by omega) h
          · -- n >= 508812949
            exact Brocard.berndt_galway_chunk_2830 n m (by omega) (by omega) h
        · -- n >= 508992805
          rcases Nat.lt_or_ge n 509352517 with hs4 | hs4
          · -- n < 509352517
            rcases Nat.lt_or_ge n 509172661 with hs5 | hs5
            · -- n < 509172661
              exact Brocard.berndt_galway_chunk_2831 n m (by omega) (by omega) h
            · -- n >= 509172661
              exact Brocard.berndt_galway_chunk_2832 n m (by omega) (by omega) h
          · -- n >= 509352517
            exact Brocard.berndt_galway_chunk_2833 n m (by omega) (by omega) h
      · -- n >= 509532374
        rcases Nat.lt_or_ge n 510071942 with hs3 | hs3
        · -- n < 510071942
          rcases Nat.lt_or_ge n 509892086 with hs4 | hs4
          · -- n < 509892086
            rcases Nat.lt_or_ge n 509712230 with hs5 | hs5
            · -- n < 509712230
              exact Brocard.berndt_galway_chunk_2834 n m (by omega) (by omega) h
            · -- n >= 509712230
              exact Brocard.berndt_galway_chunk_2835 n m (by omega) (by omega) h
          · -- n >= 509892086
            exact Brocard.berndt_galway_chunk_2836 n m (by omega) (by omega) h
        · -- n >= 510071942
          rcases Nat.lt_or_ge n 510431654 with hs4 | hs4
          · -- n < 510431654
            rcases Nat.lt_or_ge n 510251798 with hs5 | hs5
            · -- n < 510251798
              exact Brocard.berndt_galway_chunk_2837 n m (by omega) (by omega) h
            · -- n >= 510251798
              exact Brocard.berndt_galway_chunk_2838 n m (by omega) (by omega) h
          · -- n >= 510431654
            exact Brocard.berndt_galway_chunk_2839 n m (by omega) (by omega) h
    · -- n >= 510611510
      rcases Nat.lt_or_ge n 511690647 with hs2 | hs2
      · -- n < 511690647
        rcases Nat.lt_or_ge n 511151079 with hs3 | hs3
        · -- n < 511151079
          rcases Nat.lt_or_ge n 510971223 with hs4 | hs4
          · -- n < 510971223
            rcases Nat.lt_or_ge n 510791366 with hs5 | hs5
            · -- n < 510791366
              exact Brocard.berndt_galway_chunk_2840 n m (by omega) (by omega) h
            · -- n >= 510791366
              exact Brocard.berndt_galway_chunk_2841 n m (by omega) (by omega) h
          · -- n >= 510971223
            exact Brocard.berndt_galway_chunk_2842 n m (by omega) (by omega) h
        · -- n >= 511151079
          rcases Nat.lt_or_ge n 511510791 with hs4 | hs4
          · -- n < 511510791
            rcases Nat.lt_or_ge n 511330935 with hs5 | hs5
            · -- n < 511330935
              exact Brocard.berndt_galway_chunk_2843 n m (by omega) (by omega) h
            · -- n >= 511330935
              exact Brocard.berndt_galway_chunk_2844 n m (by omega) (by omega) h
          · -- n >= 511510791
            exact Brocard.berndt_galway_chunk_2845 n m (by omega) (by omega) h
      · -- n >= 511690647
        rcases Nat.lt_or_ge n 512230215 with hs3 | hs3
        · -- n < 512230215
          rcases Nat.lt_or_ge n 512050359 with hs4 | hs4
          · -- n < 512050359
            rcases Nat.lt_or_ge n 511870503 with hs5 | hs5
            · -- n < 511870503
              exact Brocard.berndt_galway_chunk_2846 n m (by omega) (by omega) h
            · -- n >= 511870503
              exact Brocard.berndt_galway_chunk_2847 n m (by omega) (by omega) h
          · -- n >= 512050359
            exact Brocard.berndt_galway_chunk_2848 n m (by omega) (by omega) h
        · -- n >= 512230215
          rcases Nat.lt_or_ge n 512589928 with hs4 | hs4
          · -- n < 512589928
            rcases Nat.lt_or_ge n 512410071 with hs5 | hs5
            · -- n < 512410071
              exact Brocard.berndt_galway_chunk_2849 n m (by omega) (by omega) h
            · -- n >= 512410071
              exact Brocard.berndt_galway_chunk_2850 n m (by omega) (by omega) h
          · -- n >= 512589928
            exact Brocard.berndt_galway_chunk_2851 n m (by omega) (by omega) h
  · -- n >= 512769784
    rcases Nat.lt_or_ge n 514928057 with hs1 | hs1
    · -- n < 514928057
      rcases Nat.lt_or_ge n 513848920 with hs2 | hs2
      · -- n < 513848920
        rcases Nat.lt_or_ge n 513309352 with hs3 | hs3
        · -- n < 513309352
          rcases Nat.lt_or_ge n 513129496 with hs4 | hs4
          · -- n < 513129496
            rcases Nat.lt_or_ge n 512949640 with hs5 | hs5
            · -- n < 512949640
              exact Brocard.berndt_galway_chunk_2852 n m (by omega) (by omega) h
            · -- n >= 512949640
              exact Brocard.berndt_galway_chunk_2853 n m (by omega) (by omega) h
          · -- n >= 513129496
            exact Brocard.berndt_galway_chunk_2854 n m (by omega) (by omega) h
        · -- n >= 513309352
          rcases Nat.lt_or_ge n 513669064 with hs4 | hs4
          · -- n < 513669064
            rcases Nat.lt_or_ge n 513489208 with hs5 | hs5
            · -- n < 513489208
              exact Brocard.berndt_galway_chunk_2855 n m (by omega) (by omega) h
            · -- n >= 513489208
              exact Brocard.berndt_galway_chunk_2856 n m (by omega) (by omega) h
          · -- n >= 513669064
            exact Brocard.berndt_galway_chunk_2857 n m (by omega) (by omega) h
      · -- n >= 513848920
        rcases Nat.lt_or_ge n 514388489 with hs3 | hs3
        · -- n < 514388489
          rcases Nat.lt_or_ge n 514208633 with hs4 | hs4
          · -- n < 514208633
            rcases Nat.lt_or_ge n 514028776 with hs5 | hs5
            · -- n < 514028776
              exact Brocard.berndt_galway_chunk_2858 n m (by omega) (by omega) h
            · -- n >= 514028776
              exact Brocard.berndt_galway_chunk_2859 n m (by omega) (by omega) h
          · -- n >= 514208633
            exact Brocard.berndt_galway_chunk_2860 n m (by omega) (by omega) h
        · -- n >= 514388489
          rcases Nat.lt_or_ge n 514748201 with hs4 | hs4
          · -- n < 514748201
            rcases Nat.lt_or_ge n 514568345 with hs5 | hs5
            · -- n < 514568345
              exact Brocard.berndt_galway_chunk_2861 n m (by omega) (by omega) h
            · -- n >= 514568345
              exact Brocard.berndt_galway_chunk_2862 n m (by omega) (by omega) h
          · -- n >= 514748201
            exact Brocard.berndt_galway_chunk_2863 n m (by omega) (by omega) h
    · -- n >= 514928057
      rcases Nat.lt_or_ge n 516007194 with hs2 | hs2
      · -- n < 516007194
        rcases Nat.lt_or_ge n 515467625 with hs3 | hs3
        · -- n < 515467625
          rcases Nat.lt_or_ge n 515287769 with hs4 | hs4
          · -- n < 515287769
            rcases Nat.lt_or_ge n 515107913 with hs5 | hs5
            · -- n < 515107913
              exact Brocard.berndt_galway_chunk_2864 n m (by omega) (by omega) h
            · -- n >= 515107913
              exact Brocard.berndt_galway_chunk_2865 n m (by omega) (by omega) h
          · -- n >= 515287769
            exact Brocard.berndt_galway_chunk_2866 n m (by omega) (by omega) h
        · -- n >= 515467625
          rcases Nat.lt_or_ge n 515827338 with hs4 | hs4
          · -- n < 515827338
            rcases Nat.lt_or_ge n 515647482 with hs5 | hs5
            · -- n < 515647482
              exact Brocard.berndt_galway_chunk_2867 n m (by omega) (by omega) h
            · -- n >= 515647482
              exact Brocard.berndt_galway_chunk_2868 n m (by omega) (by omega) h
          · -- n >= 515827338
            exact Brocard.berndt_galway_chunk_2869 n m (by omega) (by omega) h
      · -- n >= 516007194
        rcases Nat.lt_or_ge n 516546762 with hs3 | hs3
        · -- n < 516546762
          rcases Nat.lt_or_ge n 516366906 with hs4 | hs4
          · -- n < 516366906
            rcases Nat.lt_or_ge n 516187050 with hs5 | hs5
            · -- n < 516187050
              exact Brocard.berndt_galway_chunk_2870 n m (by omega) (by omega) h
            · -- n >= 516187050
              exact Brocard.berndt_galway_chunk_2871 n m (by omega) (by omega) h
          · -- n >= 516366906
            exact Brocard.berndt_galway_chunk_2872 n m (by omega) (by omega) h
        · -- n >= 516546762
          rcases Nat.lt_or_ge n 516726618 with hs4 | hs4
          · -- n < 516726618
            exact Brocard.berndt_galway_chunk_2873 n m (by omega) (by omega) h
          · -- n >= 516726618
            exact Brocard.berndt_galway_chunk_2874 n m (by omega) (by omega) h
