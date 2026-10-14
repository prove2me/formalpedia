-- Prove2me | solution 1 for Brocard.berndt_galway_group_039
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:51:43.047107+00:00
-- url     : https://prove2.me/submissions/3a8cd376-291f-4271-8ee9-330440aae638

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1763
import Theorems.Thm_Brocard_berndt_galway_chunk_1764
import Theorems.Thm_Brocard_berndt_galway_chunk_1765
import Theorems.Thm_Brocard_berndt_galway_chunk_1766
import Theorems.Thm_Brocard_berndt_galway_chunk_1767
import Theorems.Thm_Brocard_berndt_galway_chunk_1768
import Theorems.Thm_Brocard_berndt_galway_chunk_1769
import Theorems.Thm_Brocard_berndt_galway_chunk_1770
import Theorems.Thm_Brocard_berndt_galway_chunk_1771
import Theorems.Thm_Brocard_berndt_galway_chunk_1772
import Theorems.Thm_Brocard_berndt_galway_chunk_1773
import Theorems.Thm_Brocard_berndt_galway_chunk_1774
import Theorems.Thm_Brocard_berndt_galway_chunk_1775
import Theorems.Thm_Brocard_berndt_galway_chunk_1776
import Theorems.Thm_Brocard_berndt_galway_chunk_1777
import Theorems.Thm_Brocard_berndt_galway_chunk_1778
import Theorems.Thm_Brocard_berndt_galway_chunk_1779
import Theorems.Thm_Brocard_berndt_galway_chunk_1780
import Theorems.Thm_Brocard_berndt_galway_chunk_1781
import Theorems.Thm_Brocard_berndt_galway_chunk_1782
import Theorems.Thm_Brocard_berndt_galway_chunk_1783
import Theorems.Thm_Brocard_berndt_galway_chunk_1784
import Theorems.Thm_Brocard_berndt_galway_chunk_1785
import Theorems.Thm_Brocard_berndt_galway_chunk_1786
import Theorems.Thm_Brocard_berndt_galway_chunk_1787
import Theorems.Thm_Brocard_berndt_galway_chunk_1788
import Theorems.Thm_Brocard_berndt_galway_chunk_1789
import Theorems.Thm_Brocard_berndt_galway_chunk_1790
import Theorems.Thm_Brocard_berndt_galway_chunk_1791
import Theorems.Thm_Brocard_berndt_galway_chunk_1792
import Theorems.Thm_Brocard_berndt_galway_chunk_1793
import Theorems.Thm_Brocard_berndt_galway_chunk_1794
import Theorems.Thm_Brocard_berndt_galway_chunk_1795
import Theorems.Thm_Brocard_berndt_galway_chunk_1796
import Theorems.Thm_Brocard_berndt_galway_chunk_1797
import Theorems.Thm_Brocard_berndt_galway_chunk_1798
import Theorems.Thm_Brocard_berndt_galway_chunk_1799
import Theorems.Thm_Brocard_berndt_galway_chunk_1800
import Theorems.Thm_Brocard_berndt_galway_chunk_1801
import Theorems.Thm_Brocard_berndt_galway_chunk_1802
import Theorems.Thm_Brocard_berndt_galway_chunk_1803
import Theorems.Thm_Brocard_berndt_galway_chunk_1804
import Theorems.Thm_Brocard_berndt_galway_chunk_1805
import Theorems.Thm_Brocard_berndt_galway_chunk_1806
import Theorems.Thm_Brocard_berndt_galway_chunk_1807
import Theorems.Thm_Brocard_berndt_galway_chunk_1808
import Theorems.Thm_Brocard_berndt_galway_chunk_1809

theorem solution (n m : ℕ) (h1 : 316906474 ≤ n) (h2 : n < 325359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 321223021 with hs0 | hs0
  · -- n < 321223021
    rcases Nat.lt_or_ge n 319064748 with hs1 | hs1
    · -- n < 319064748
      rcases Nat.lt_or_ge n 317985611 with hs2 | hs2
      · -- n < 317985611
        rcases Nat.lt_or_ge n 317446043 with hs3 | hs3
        · -- n < 317446043
          rcases Nat.lt_or_ge n 317266187 with hs4 | hs4
          · -- n < 317266187
            rcases Nat.lt_or_ge n 317086330 with hs5 | hs5
            · -- n < 317086330
              exact Brocard.berndt_galway_chunk_1763 n m (by omega) (by omega) h
            · -- n >= 317086330
              exact Brocard.berndt_galway_chunk_1764 n m (by omega) (by omega) h
          · -- n >= 317266187
            exact Brocard.berndt_galway_chunk_1765 n m (by omega) (by omega) h
        · -- n >= 317446043
          rcases Nat.lt_or_ge n 317805755 with hs4 | hs4
          · -- n < 317805755
            rcases Nat.lt_or_ge n 317625899 with hs5 | hs5
            · -- n < 317625899
              exact Brocard.berndt_galway_chunk_1766 n m (by omega) (by omega) h
            · -- n >= 317625899
              exact Brocard.berndt_galway_chunk_1767 n m (by omega) (by omega) h
          · -- n >= 317805755
            exact Brocard.berndt_galway_chunk_1768 n m (by omega) (by omega) h
      · -- n >= 317985611
        rcases Nat.lt_or_ge n 318525179 with hs3 | hs3
        · -- n < 318525179
          rcases Nat.lt_or_ge n 318345323 with hs4 | hs4
          · -- n < 318345323
            rcases Nat.lt_or_ge n 318165467 with hs5 | hs5
            · -- n < 318165467
              exact Brocard.berndt_galway_chunk_1769 n m (by omega) (by omega) h
            · -- n >= 318165467
              exact Brocard.berndt_galway_chunk_1770 n m (by omega) (by omega) h
          · -- n >= 318345323
            exact Brocard.berndt_galway_chunk_1771 n m (by omega) (by omega) h
        · -- n >= 318525179
          rcases Nat.lt_or_ge n 318884892 with hs4 | hs4
          · -- n < 318884892
            rcases Nat.lt_or_ge n 318705035 with hs5 | hs5
            · -- n < 318705035
              exact Brocard.berndt_galway_chunk_1772 n m (by omega) (by omega) h
            · -- n >= 318705035
              exact Brocard.berndt_galway_chunk_1773 n m (by omega) (by omega) h
          · -- n >= 318884892
            exact Brocard.berndt_galway_chunk_1774 n m (by omega) (by omega) h
    · -- n >= 319064748
      rcases Nat.lt_or_ge n 320143884 with hs2 | hs2
      · -- n < 320143884
        rcases Nat.lt_or_ge n 319604316 with hs3 | hs3
        · -- n < 319604316
          rcases Nat.lt_or_ge n 319424460 with hs4 | hs4
          · -- n < 319424460
            rcases Nat.lt_or_ge n 319244604 with hs5 | hs5
            · -- n < 319244604
              exact Brocard.berndt_galway_chunk_1775 n m (by omega) (by omega) h
            · -- n >= 319244604
              exact Brocard.berndt_galway_chunk_1776 n m (by omega) (by omega) h
          · -- n >= 319424460
            exact Brocard.berndt_galway_chunk_1777 n m (by omega) (by omega) h
        · -- n >= 319604316
          rcases Nat.lt_or_ge n 319964028 with hs4 | hs4
          · -- n < 319964028
            rcases Nat.lt_or_ge n 319784172 with hs5 | hs5
            · -- n < 319784172
              exact Brocard.berndt_galway_chunk_1778 n m (by omega) (by omega) h
            · -- n >= 319784172
              exact Brocard.berndt_galway_chunk_1779 n m (by omega) (by omega) h
          · -- n >= 319964028
            exact Brocard.berndt_galway_chunk_1780 n m (by omega) (by omega) h
      · -- n >= 320143884
        rcases Nat.lt_or_ge n 320683453 with hs3 | hs3
        · -- n < 320683453
          rcases Nat.lt_or_ge n 320503597 with hs4 | hs4
          · -- n < 320503597
            rcases Nat.lt_or_ge n 320323741 with hs5 | hs5
            · -- n < 320323741
              exact Brocard.berndt_galway_chunk_1781 n m (by omega) (by omega) h
            · -- n >= 320323741
              exact Brocard.berndt_galway_chunk_1782 n m (by omega) (by omega) h
          · -- n >= 320503597
            exact Brocard.berndt_galway_chunk_1783 n m (by omega) (by omega) h
        · -- n >= 320683453
          rcases Nat.lt_or_ge n 321043165 with hs4 | hs4
          · -- n < 321043165
            rcases Nat.lt_or_ge n 320863309 with hs5 | hs5
            · -- n < 320863309
              exact Brocard.berndt_galway_chunk_1784 n m (by omega) (by omega) h
            · -- n >= 320863309
              exact Brocard.berndt_galway_chunk_1785 n m (by omega) (by omega) h
          · -- n >= 321043165
            exact Brocard.berndt_galway_chunk_1786 n m (by omega) (by omega) h
  · -- n >= 321223021
    rcases Nat.lt_or_ge n 323381294 with hs1 | hs1
    · -- n < 323381294
      rcases Nat.lt_or_ge n 322302158 with hs2 | hs2
      · -- n < 322302158
        rcases Nat.lt_or_ge n 321762589 with hs3 | hs3
        · -- n < 321762589
          rcases Nat.lt_or_ge n 321582733 with hs4 | hs4
          · -- n < 321582733
            rcases Nat.lt_or_ge n 321402877 with hs5 | hs5
            · -- n < 321402877
              exact Brocard.berndt_galway_chunk_1787 n m (by omega) (by omega) h
            · -- n >= 321402877
              exact Brocard.berndt_galway_chunk_1788 n m (by omega) (by omega) h
          · -- n >= 321582733
            exact Brocard.berndt_galway_chunk_1789 n m (by omega) (by omega) h
        · -- n >= 321762589
          rcases Nat.lt_or_ge n 322122302 with hs4 | hs4
          · -- n < 322122302
            rcases Nat.lt_or_ge n 321942446 with hs5 | hs5
            · -- n < 321942446
              exact Brocard.berndt_galway_chunk_1790 n m (by omega) (by omega) h
            · -- n >= 321942446
              exact Brocard.berndt_galway_chunk_1791 n m (by omega) (by omega) h
          · -- n >= 322122302
            exact Brocard.berndt_galway_chunk_1792 n m (by omega) (by omega) h
      · -- n >= 322302158
        rcases Nat.lt_or_ge n 322841726 with hs3 | hs3
        · -- n < 322841726
          rcases Nat.lt_or_ge n 322661870 with hs4 | hs4
          · -- n < 322661870
            rcases Nat.lt_or_ge n 322482014 with hs5 | hs5
            · -- n < 322482014
              exact Brocard.berndt_galway_chunk_1793 n m (by omega) (by omega) h
            · -- n >= 322482014
              exact Brocard.berndt_galway_chunk_1794 n m (by omega) (by omega) h
          · -- n >= 322661870
            exact Brocard.berndt_galway_chunk_1795 n m (by omega) (by omega) h
        · -- n >= 322841726
          rcases Nat.lt_or_ge n 323201438 with hs4 | hs4
          · -- n < 323201438
            rcases Nat.lt_or_ge n 323021582 with hs5 | hs5
            · -- n < 323021582
              exact Brocard.berndt_galway_chunk_1796 n m (by omega) (by omega) h
            · -- n >= 323021582
              exact Brocard.berndt_galway_chunk_1797 n m (by omega) (by omega) h
          · -- n >= 323201438
            exact Brocard.berndt_galway_chunk_1798 n m (by omega) (by omega) h
    · -- n >= 323381294
      rcases Nat.lt_or_ge n 324460431 with hs2 | hs2
      · -- n < 324460431
        rcases Nat.lt_or_ge n 323920863 with hs3 | hs3
        · -- n < 323920863
          rcases Nat.lt_or_ge n 323741007 with hs4 | hs4
          · -- n < 323741007
            rcases Nat.lt_or_ge n 323561151 with hs5 | hs5
            · -- n < 323561151
              exact Brocard.berndt_galway_chunk_1799 n m (by omega) (by omega) h
            · -- n >= 323561151
              exact Brocard.berndt_galway_chunk_1800 n m (by omega) (by omega) h
          · -- n >= 323741007
            exact Brocard.berndt_galway_chunk_1801 n m (by omega) (by omega) h
        · -- n >= 323920863
          rcases Nat.lt_or_ge n 324280575 with hs4 | hs4
          · -- n < 324280575
            rcases Nat.lt_or_ge n 324100719 with hs5 | hs5
            · -- n < 324100719
              exact Brocard.berndt_galway_chunk_1802 n m (by omega) (by omega) h
            · -- n >= 324100719
              exact Brocard.berndt_galway_chunk_1803 n m (by omega) (by omega) h
          · -- n >= 324280575
            exact Brocard.berndt_galway_chunk_1804 n m (by omega) (by omega) h
      · -- n >= 324460431
        rcases Nat.lt_or_ge n 325000000 with hs3 | hs3
        · -- n < 325000000
          rcases Nat.lt_or_ge n 324820143 with hs4 | hs4
          · -- n < 324820143
            rcases Nat.lt_or_ge n 324640287 with hs5 | hs5
            · -- n < 324640287
              exact Brocard.berndt_galway_chunk_1805 n m (by omega) (by omega) h
            · -- n >= 324640287
              exact Brocard.berndt_galway_chunk_1806 n m (by omega) (by omega) h
          · -- n >= 324820143
            exact Brocard.berndt_galway_chunk_1807 n m (by omega) (by omega) h
        · -- n >= 325000000
          rcases Nat.lt_or_ge n 325179856 with hs4 | hs4
          · -- n < 325179856
            exact Brocard.berndt_galway_chunk_1808 n m (by omega) (by omega) h
          · -- n >= 325179856
            exact Brocard.berndt_galway_chunk_1809 n m (by omega) (by omega) h
