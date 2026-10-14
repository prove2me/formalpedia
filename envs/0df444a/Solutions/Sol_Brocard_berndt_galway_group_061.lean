-- Prove2me | solution 1 for Brocard.berndt_galway_group_061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:56:57.678372+00:00
-- url     : https://prove2.me/submissions/ef2a2894-4631-47ee-ac72-4cf20d625a26

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2781
import Theorems.Thm_Brocard_berndt_galway_chunk_2782
import Theorems.Thm_Brocard_berndt_galway_chunk_2783
import Theorems.Thm_Brocard_berndt_galway_chunk_2784
import Theorems.Thm_Brocard_berndt_galway_chunk_2785
import Theorems.Thm_Brocard_berndt_galway_chunk_2786
import Theorems.Thm_Brocard_berndt_galway_chunk_2787
import Theorems.Thm_Brocard_berndt_galway_chunk_2788
import Theorems.Thm_Brocard_berndt_galway_chunk_2789
import Theorems.Thm_Brocard_berndt_galway_chunk_2790
import Theorems.Thm_Brocard_berndt_galway_chunk_2791
import Theorems.Thm_Brocard_berndt_galway_chunk_2792
import Theorems.Thm_Brocard_berndt_galway_chunk_2793
import Theorems.Thm_Brocard_berndt_galway_chunk_2794
import Theorems.Thm_Brocard_berndt_galway_chunk_2795
import Theorems.Thm_Brocard_berndt_galway_chunk_2796
import Theorems.Thm_Brocard_berndt_galway_chunk_2797
import Theorems.Thm_Brocard_berndt_galway_chunk_2798
import Theorems.Thm_Brocard_berndt_galway_chunk_2799
import Theorems.Thm_Brocard_berndt_galway_chunk_2800
import Theorems.Thm_Brocard_berndt_galway_chunk_2801
import Theorems.Thm_Brocard_berndt_galway_chunk_2802
import Theorems.Thm_Brocard_berndt_galway_chunk_2803
import Theorems.Thm_Brocard_berndt_galway_chunk_2804
import Theorems.Thm_Brocard_berndt_galway_chunk_2805
import Theorems.Thm_Brocard_berndt_galway_chunk_2806
import Theorems.Thm_Brocard_berndt_galway_chunk_2807
import Theorems.Thm_Brocard_berndt_galway_chunk_2808
import Theorems.Thm_Brocard_berndt_galway_chunk_2809
import Theorems.Thm_Brocard_berndt_galway_chunk_2810
import Theorems.Thm_Brocard_berndt_galway_chunk_2811
import Theorems.Thm_Brocard_berndt_galway_chunk_2812
import Theorems.Thm_Brocard_berndt_galway_chunk_2813
import Theorems.Thm_Brocard_berndt_galway_chunk_2814
import Theorems.Thm_Brocard_berndt_galway_chunk_2815
import Theorems.Thm_Brocard_berndt_galway_chunk_2816
import Theorems.Thm_Brocard_berndt_galway_chunk_2817
import Theorems.Thm_Brocard_berndt_galway_chunk_2818
import Theorems.Thm_Brocard_berndt_galway_chunk_2819
import Theorems.Thm_Brocard_berndt_galway_chunk_2820
import Theorems.Thm_Brocard_berndt_galway_chunk_2821
import Theorems.Thm_Brocard_berndt_galway_chunk_2822
import Theorems.Thm_Brocard_berndt_galway_chunk_2823
import Theorems.Thm_Brocard_berndt_galway_chunk_2824
import Theorems.Thm_Brocard_berndt_galway_chunk_2825
import Theorems.Thm_Brocard_berndt_galway_chunk_2826
import Theorems.Thm_Brocard_berndt_galway_chunk_2827

theorem solution (n m : ℕ) (h1 : 500000000 ≤ n) (h2 : n < 508453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 504316546 with hs0 | hs0
  · -- n < 504316546
    rcases Nat.lt_or_ge n 502158273 with hs1 | hs1
    · -- n < 502158273
      rcases Nat.lt_or_ge n 501079136 with hs2 | hs2
      · -- n < 501079136
        rcases Nat.lt_or_ge n 500539568 with hs3 | hs3
        · -- n < 500539568
          rcases Nat.lt_or_ge n 500359712 with hs4 | hs4
          · -- n < 500359712
            rcases Nat.lt_or_ge n 500179856 with hs5 | hs5
            · -- n < 500179856
              exact Brocard.berndt_galway_chunk_2781 n m (by omega) (by omega) h
            · -- n >= 500179856
              exact Brocard.berndt_galway_chunk_2782 n m (by omega) (by omega) h
          · -- n >= 500359712
            exact Brocard.berndt_galway_chunk_2783 n m (by omega) (by omega) h
        · -- n >= 500539568
          rcases Nat.lt_or_ge n 500899280 with hs4 | hs4
          · -- n < 500899280
            rcases Nat.lt_or_ge n 500719424 with hs5 | hs5
            · -- n < 500719424
              exact Brocard.berndt_galway_chunk_2784 n m (by omega) (by omega) h
            · -- n >= 500719424
              exact Brocard.berndt_galway_chunk_2785 n m (by omega) (by omega) h
          · -- n >= 500899280
            exact Brocard.berndt_galway_chunk_2786 n m (by omega) (by omega) h
      · -- n >= 501079136
        rcases Nat.lt_or_ge n 501618705 with hs3 | hs3
        · -- n < 501618705
          rcases Nat.lt_or_ge n 501438848 with hs4 | hs4
          · -- n < 501438848
            rcases Nat.lt_or_ge n 501258992 with hs5 | hs5
            · -- n < 501258992
              exact Brocard.berndt_galway_chunk_2787 n m (by omega) (by omega) h
            · -- n >= 501258992
              exact Brocard.berndt_galway_chunk_2788 n m (by omega) (by omega) h
          · -- n >= 501438848
            exact Brocard.berndt_galway_chunk_2789 n m (by omega) (by omega) h
        · -- n >= 501618705
          rcases Nat.lt_or_ge n 501978417 with hs4 | hs4
          · -- n < 501978417
            rcases Nat.lt_or_ge n 501798561 with hs5 | hs5
            · -- n < 501798561
              exact Brocard.berndt_galway_chunk_2790 n m (by omega) (by omega) h
            · -- n >= 501798561
              exact Brocard.berndt_galway_chunk_2791 n m (by omega) (by omega) h
          · -- n >= 501978417
            exact Brocard.berndt_galway_chunk_2792 n m (by omega) (by omega) h
    · -- n >= 502158273
      rcases Nat.lt_or_ge n 503237410 with hs2 | hs2
      · -- n < 503237410
        rcases Nat.lt_or_ge n 502697841 with hs3 | hs3
        · -- n < 502697841
          rcases Nat.lt_or_ge n 502517985 with hs4 | hs4
          · -- n < 502517985
            rcases Nat.lt_or_ge n 502338129 with hs5 | hs5
            · -- n < 502338129
              exact Brocard.berndt_galway_chunk_2793 n m (by omega) (by omega) h
            · -- n >= 502338129
              exact Brocard.berndt_galway_chunk_2794 n m (by omega) (by omega) h
          · -- n >= 502517985
            exact Brocard.berndt_galway_chunk_2795 n m (by omega) (by omega) h
        · -- n >= 502697841
          rcases Nat.lt_or_ge n 503057553 with hs4 | hs4
          · -- n < 503057553
            rcases Nat.lt_or_ge n 502877697 with hs5 | hs5
            · -- n < 502877697
              exact Brocard.berndt_galway_chunk_2796 n m (by omega) (by omega) h
            · -- n >= 502877697
              exact Brocard.berndt_galway_chunk_2797 n m (by omega) (by omega) h
          · -- n >= 503057553
            exact Brocard.berndt_galway_chunk_2798 n m (by omega) (by omega) h
      · -- n >= 503237410
        rcases Nat.lt_or_ge n 503776978 with hs3 | hs3
        · -- n < 503776978
          rcases Nat.lt_or_ge n 503597122 with hs4 | hs4
          · -- n < 503597122
            rcases Nat.lt_or_ge n 503417266 with hs5 | hs5
            · -- n < 503417266
              exact Brocard.berndt_galway_chunk_2799 n m (by omega) (by omega) h
            · -- n >= 503417266
              exact Brocard.berndt_galway_chunk_2800 n m (by omega) (by omega) h
          · -- n >= 503597122
            exact Brocard.berndt_galway_chunk_2801 n m (by omega) (by omega) h
        · -- n >= 503776978
          rcases Nat.lt_or_ge n 504136690 with hs4 | hs4
          · -- n < 504136690
            rcases Nat.lt_or_ge n 503956834 with hs5 | hs5
            · -- n < 503956834
              exact Brocard.berndt_galway_chunk_2802 n m (by omega) (by omega) h
            · -- n >= 503956834
              exact Brocard.berndt_galway_chunk_2803 n m (by omega) (by omega) h
          · -- n >= 504136690
            exact Brocard.berndt_galway_chunk_2804 n m (by omega) (by omega) h
  · -- n >= 504316546
    rcases Nat.lt_or_ge n 506474820 with hs1 | hs1
    · -- n < 506474820
      rcases Nat.lt_or_ge n 505395683 with hs2 | hs2
      · -- n < 505395683
        rcases Nat.lt_or_ge n 504856115 with hs3 | hs3
        · -- n < 504856115
          rcases Nat.lt_or_ge n 504676258 with hs4 | hs4
          · -- n < 504676258
            rcases Nat.lt_or_ge n 504496402 with hs5 | hs5
            · -- n < 504496402
              exact Brocard.berndt_galway_chunk_2805 n m (by omega) (by omega) h
            · -- n >= 504496402
              exact Brocard.berndt_galway_chunk_2806 n m (by omega) (by omega) h
          · -- n >= 504676258
            exact Brocard.berndt_galway_chunk_2807 n m (by omega) (by omega) h
        · -- n >= 504856115
          rcases Nat.lt_or_ge n 505215827 with hs4 | hs4
          · -- n < 505215827
            rcases Nat.lt_or_ge n 505035971 with hs5 | hs5
            · -- n < 505035971
              exact Brocard.berndt_galway_chunk_2808 n m (by omega) (by omega) h
            · -- n >= 505035971
              exact Brocard.berndt_galway_chunk_2809 n m (by omega) (by omega) h
          · -- n >= 505215827
            exact Brocard.berndt_galway_chunk_2810 n m (by omega) (by omega) h
      · -- n >= 505395683
        rcases Nat.lt_or_ge n 505935251 with hs3 | hs3
        · -- n < 505935251
          rcases Nat.lt_or_ge n 505755395 with hs4 | hs4
          · -- n < 505755395
            rcases Nat.lt_or_ge n 505575539 with hs5 | hs5
            · -- n < 505575539
              exact Brocard.berndt_galway_chunk_2811 n m (by omega) (by omega) h
            · -- n >= 505575539
              exact Brocard.berndt_galway_chunk_2812 n m (by omega) (by omega) h
          · -- n >= 505755395
            exact Brocard.berndt_galway_chunk_2813 n m (by omega) (by omega) h
        · -- n >= 505935251
          rcases Nat.lt_or_ge n 506294964 with hs4 | hs4
          · -- n < 506294964
            rcases Nat.lt_or_ge n 506115107 with hs5 | hs5
            · -- n < 506115107
              exact Brocard.berndt_galway_chunk_2814 n m (by omega) (by omega) h
            · -- n >= 506115107
              exact Brocard.berndt_galway_chunk_2815 n m (by omega) (by omega) h
          · -- n >= 506294964
            exact Brocard.berndt_galway_chunk_2816 n m (by omega) (by omega) h
    · -- n >= 506474820
      rcases Nat.lt_or_ge n 507553956 with hs2 | hs2
      · -- n < 507553956
        rcases Nat.lt_or_ge n 507014388 with hs3 | hs3
        · -- n < 507014388
          rcases Nat.lt_or_ge n 506834532 with hs4 | hs4
          · -- n < 506834532
            rcases Nat.lt_or_ge n 506654676 with hs5 | hs5
            · -- n < 506654676
              exact Brocard.berndt_galway_chunk_2817 n m (by omega) (by omega) h
            · -- n >= 506654676
              exact Brocard.berndt_galway_chunk_2818 n m (by omega) (by omega) h
          · -- n >= 506834532
            exact Brocard.berndt_galway_chunk_2819 n m (by omega) (by omega) h
        · -- n >= 507014388
          rcases Nat.lt_or_ge n 507374100 with hs4 | hs4
          · -- n < 507374100
            rcases Nat.lt_or_ge n 507194244 with hs5 | hs5
            · -- n < 507194244
              exact Brocard.berndt_galway_chunk_2820 n m (by omega) (by omega) h
            · -- n >= 507194244
              exact Brocard.berndt_galway_chunk_2821 n m (by omega) (by omega) h
          · -- n >= 507374100
            exact Brocard.berndt_galway_chunk_2822 n m (by omega) (by omega) h
      · -- n >= 507553956
        rcases Nat.lt_or_ge n 508093525 with hs3 | hs3
        · -- n < 508093525
          rcases Nat.lt_or_ge n 507913669 with hs4 | hs4
          · -- n < 507913669
            rcases Nat.lt_or_ge n 507733812 with hs5 | hs5
            · -- n < 507733812
              exact Brocard.berndt_galway_chunk_2823 n m (by omega) (by omega) h
            · -- n >= 507733812
              exact Brocard.berndt_galway_chunk_2824 n m (by omega) (by omega) h
          · -- n >= 507913669
            exact Brocard.berndt_galway_chunk_2825 n m (by omega) (by omega) h
        · -- n >= 508093525
          rcases Nat.lt_or_ge n 508273381 with hs4 | hs4
          · -- n < 508273381
            exact Brocard.berndt_galway_chunk_2826 n m (by omega) (by omega) h
          · -- n >= 508273381
            exact Brocard.berndt_galway_chunk_2827 n m (by omega) (by omega) h
