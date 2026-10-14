-- Prove2me | solution 1 for Brocard.berndt_galway_group_036
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:14:10.203888+00:00
-- url     : https://prove2.me/submissions/591ae103-f7ee-498b-b0e6-82d4a3f32ad0

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1623
import Theorems.Thm_Brocard_berndt_galway_chunk_1624
import Theorems.Thm_Brocard_berndt_galway_chunk_1625
import Theorems.Thm_Brocard_berndt_galway_chunk_1626
import Theorems.Thm_Brocard_berndt_galway_chunk_1627
import Theorems.Thm_Brocard_berndt_galway_chunk_1628
import Theorems.Thm_Brocard_berndt_galway_chunk_1629
import Theorems.Thm_Brocard_berndt_galway_chunk_1630
import Theorems.Thm_Brocard_berndt_galway_chunk_1631
import Theorems.Thm_Brocard_berndt_galway_chunk_1632
import Theorems.Thm_Brocard_berndt_galway_chunk_1633
import Theorems.Thm_Brocard_berndt_galway_chunk_1634
import Theorems.Thm_Brocard_berndt_galway_chunk_1635
import Theorems.Thm_Brocard_berndt_galway_chunk_1636
import Theorems.Thm_Brocard_berndt_galway_chunk_1637
import Theorems.Thm_Brocard_berndt_galway_chunk_1638
import Theorems.Thm_Brocard_berndt_galway_chunk_1639
import Theorems.Thm_Brocard_berndt_galway_chunk_1640
import Theorems.Thm_Brocard_berndt_galway_chunk_1641
import Theorems.Thm_Brocard_berndt_galway_chunk_1642
import Theorems.Thm_Brocard_berndt_galway_chunk_1643
import Theorems.Thm_Brocard_berndt_galway_chunk_1644
import Theorems.Thm_Brocard_berndt_galway_chunk_1645
import Theorems.Thm_Brocard_berndt_galway_chunk_1646
import Theorems.Thm_Brocard_berndt_galway_chunk_1647
import Theorems.Thm_Brocard_berndt_galway_chunk_1648
import Theorems.Thm_Brocard_berndt_galway_chunk_1649
import Theorems.Thm_Brocard_berndt_galway_chunk_1650
import Theorems.Thm_Brocard_berndt_galway_chunk_1651
import Theorems.Thm_Brocard_berndt_galway_chunk_1652
import Theorems.Thm_Brocard_berndt_galway_chunk_1653
import Theorems.Thm_Brocard_berndt_galway_chunk_1654
import Theorems.Thm_Brocard_berndt_galway_chunk_1655
import Theorems.Thm_Brocard_berndt_galway_chunk_1656
import Theorems.Thm_Brocard_berndt_galway_chunk_1657
import Theorems.Thm_Brocard_berndt_galway_chunk_1658
import Theorems.Thm_Brocard_berndt_galway_chunk_1659
import Theorems.Thm_Brocard_berndt_galway_chunk_1660
import Theorems.Thm_Brocard_berndt_galway_chunk_1661
import Theorems.Thm_Brocard_berndt_galway_chunk_1662
import Theorems.Thm_Brocard_berndt_galway_chunk_1663
import Theorems.Thm_Brocard_berndt_galway_chunk_1664
import Theorems.Thm_Brocard_berndt_galway_chunk_1665
import Theorems.Thm_Brocard_berndt_galway_chunk_1666
import Theorems.Thm_Brocard_berndt_galway_chunk_1667
import Theorems.Thm_Brocard_berndt_galway_chunk_1668

theorem solution (n m : ℕ) (h1 : 291726618 ≤ n) (h2 : n < 300000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 295863309 with hs0 | hs0
  · -- n < 295863309
    rcases Nat.lt_or_ge n 293884892 with hs1 | hs1
    · -- n < 293884892
      rcases Nat.lt_or_ge n 292805755 with hs2 | hs2
      · -- n < 292805755
        rcases Nat.lt_or_ge n 292266187 with hs3 | hs3
        · -- n < 292266187
          rcases Nat.lt_or_ge n 292086330 with hs4 | hs4
          · -- n < 292086330
            rcases Nat.lt_or_ge n 291906474 with hs5 | hs5
            · -- n < 291906474
              exact Brocard.berndt_galway_chunk_1623 n m (by omega) (by omega) h
            · -- n >= 291906474
              exact Brocard.berndt_galway_chunk_1624 n m (by omega) (by omega) h
          · -- n >= 292086330
            exact Brocard.berndt_galway_chunk_1625 n m (by omega) (by omega) h
        · -- n >= 292266187
          rcases Nat.lt_or_ge n 292625899 with hs4 | hs4
          · -- n < 292625899
            rcases Nat.lt_or_ge n 292446043 with hs5 | hs5
            · -- n < 292446043
              exact Brocard.berndt_galway_chunk_1626 n m (by omega) (by omega) h
            · -- n >= 292446043
              exact Brocard.berndt_galway_chunk_1627 n m (by omega) (by omega) h
          · -- n >= 292625899
            exact Brocard.berndt_galway_chunk_1628 n m (by omega) (by omega) h
      · -- n >= 292805755
        rcases Nat.lt_or_ge n 293345323 with hs3 | hs3
        · -- n < 293345323
          rcases Nat.lt_or_ge n 293165467 with hs4 | hs4
          · -- n < 293165467
            rcases Nat.lt_or_ge n 292985611 with hs5 | hs5
            · -- n < 292985611
              exact Brocard.berndt_galway_chunk_1629 n m (by omega) (by omega) h
            · -- n >= 292985611
              exact Brocard.berndt_galway_chunk_1630 n m (by omega) (by omega) h
          · -- n >= 293165467
            exact Brocard.berndt_galway_chunk_1631 n m (by omega) (by omega) h
        · -- n >= 293345323
          rcases Nat.lt_or_ge n 293705035 with hs4 | hs4
          · -- n < 293705035
            rcases Nat.lt_or_ge n 293525179 with hs5 | hs5
            · -- n < 293525179
              exact Brocard.berndt_galway_chunk_1632 n m (by omega) (by omega) h
            · -- n >= 293525179
              exact Brocard.berndt_galway_chunk_1633 n m (by omega) (by omega) h
          · -- n >= 293705035
            exact Brocard.berndt_galway_chunk_1634 n m (by omega) (by omega) h
    · -- n >= 293884892
      rcases Nat.lt_or_ge n 294964028 with hs2 | hs2
      · -- n < 294964028
        rcases Nat.lt_or_ge n 294424460 with hs3 | hs3
        · -- n < 294424460
          rcases Nat.lt_or_ge n 294244604 with hs4 | hs4
          · -- n < 294244604
            rcases Nat.lt_or_ge n 294064748 with hs5 | hs5
            · -- n < 294064748
              exact Brocard.berndt_galway_chunk_1635 n m (by omega) (by omega) h
            · -- n >= 294064748
              exact Brocard.berndt_galway_chunk_1636 n m (by omega) (by omega) h
          · -- n >= 294244604
            exact Brocard.berndt_galway_chunk_1637 n m (by omega) (by omega) h
        · -- n >= 294424460
          rcases Nat.lt_or_ge n 294784172 with hs4 | hs4
          · -- n < 294784172
            rcases Nat.lt_or_ge n 294604316 with hs5 | hs5
            · -- n < 294604316
              exact Brocard.berndt_galway_chunk_1638 n m (by omega) (by omega) h
            · -- n >= 294604316
              exact Brocard.berndt_galway_chunk_1639 n m (by omega) (by omega) h
          · -- n >= 294784172
            exact Brocard.berndt_galway_chunk_1640 n m (by omega) (by omega) h
      · -- n >= 294964028
        rcases Nat.lt_or_ge n 295503597 with hs3 | hs3
        · -- n < 295503597
          rcases Nat.lt_or_ge n 295323741 with hs4 | hs4
          · -- n < 295323741
            rcases Nat.lt_or_ge n 295143884 with hs5 | hs5
            · -- n < 295143884
              exact Brocard.berndt_galway_chunk_1641 n m (by omega) (by omega) h
            · -- n >= 295143884
              exact Brocard.berndt_galway_chunk_1642 n m (by omega) (by omega) h
          · -- n >= 295323741
            exact Brocard.berndt_galway_chunk_1643 n m (by omega) (by omega) h
        · -- n >= 295503597
          rcases Nat.lt_or_ge n 295683453 with hs4 | hs4
          · -- n < 295683453
            exact Brocard.berndt_galway_chunk_1644 n m (by omega) (by omega) h
          · -- n >= 295683453
            exact Brocard.berndt_galway_chunk_1645 n m (by omega) (by omega) h
  · -- n >= 295863309
    rcases Nat.lt_or_ge n 298021582 with hs1 | hs1
    · -- n < 298021582
      rcases Nat.lt_or_ge n 296942446 with hs2 | hs2
      · -- n < 296942446
        rcases Nat.lt_or_ge n 296402877 with hs3 | hs3
        · -- n < 296402877
          rcases Nat.lt_or_ge n 296223021 with hs4 | hs4
          · -- n < 296223021
            rcases Nat.lt_or_ge n 296043165 with hs5 | hs5
            · -- n < 296043165
              exact Brocard.berndt_galway_chunk_1646 n m (by omega) (by omega) h
            · -- n >= 296043165
              exact Brocard.berndt_galway_chunk_1647 n m (by omega) (by omega) h
          · -- n >= 296223021
            exact Brocard.berndt_galway_chunk_1648 n m (by omega) (by omega) h
        · -- n >= 296402877
          rcases Nat.lt_or_ge n 296762589 with hs4 | hs4
          · -- n < 296762589
            rcases Nat.lt_or_ge n 296582733 with hs5 | hs5
            · -- n < 296582733
              exact Brocard.berndt_galway_chunk_1649 n m (by omega) (by omega) h
            · -- n >= 296582733
              exact Brocard.berndt_galway_chunk_1650 n m (by omega) (by omega) h
          · -- n >= 296762589
            exact Brocard.berndt_galway_chunk_1651 n m (by omega) (by omega) h
      · -- n >= 296942446
        rcases Nat.lt_or_ge n 297482014 with hs3 | hs3
        · -- n < 297482014
          rcases Nat.lt_or_ge n 297302158 with hs4 | hs4
          · -- n < 297302158
            rcases Nat.lt_or_ge n 297122302 with hs5 | hs5
            · -- n < 297122302
              exact Brocard.berndt_galway_chunk_1652 n m (by omega) (by omega) h
            · -- n >= 297122302
              exact Brocard.berndt_galway_chunk_1653 n m (by omega) (by omega) h
          · -- n >= 297302158
            exact Brocard.berndt_galway_chunk_1654 n m (by omega) (by omega) h
        · -- n >= 297482014
          rcases Nat.lt_or_ge n 297841726 with hs4 | hs4
          · -- n < 297841726
            rcases Nat.lt_or_ge n 297661870 with hs5 | hs5
            · -- n < 297661870
              exact Brocard.berndt_galway_chunk_1655 n m (by omega) (by omega) h
            · -- n >= 297661870
              exact Brocard.berndt_galway_chunk_1656 n m (by omega) (by omega) h
          · -- n >= 297841726
            exact Brocard.berndt_galway_chunk_1657 n m (by omega) (by omega) h
    · -- n >= 298021582
      rcases Nat.lt_or_ge n 299100719 with hs2 | hs2
      · -- n < 299100719
        rcases Nat.lt_or_ge n 298561151 with hs3 | hs3
        · -- n < 298561151
          rcases Nat.lt_or_ge n 298381294 with hs4 | hs4
          · -- n < 298381294
            rcases Nat.lt_or_ge n 298201438 with hs5 | hs5
            · -- n < 298201438
              exact Brocard.berndt_galway_chunk_1658 n m (by omega) (by omega) h
            · -- n >= 298201438
              exact Brocard.berndt_galway_chunk_1659 n m (by omega) (by omega) h
          · -- n >= 298381294
            exact Brocard.berndt_galway_chunk_1660 n m (by omega) (by omega) h
        · -- n >= 298561151
          rcases Nat.lt_or_ge n 298920863 with hs4 | hs4
          · -- n < 298920863
            rcases Nat.lt_or_ge n 298741007 with hs5 | hs5
            · -- n < 298741007
              exact Brocard.berndt_galway_chunk_1661 n m (by omega) (by omega) h
            · -- n >= 298741007
              exact Brocard.berndt_galway_chunk_1662 n m (by omega) (by omega) h
          · -- n >= 298920863
            exact Brocard.berndt_galway_chunk_1663 n m (by omega) (by omega) h
      · -- n >= 299100719
        rcases Nat.lt_or_ge n 299640287 with hs3 | hs3
        · -- n < 299640287
          rcases Nat.lt_or_ge n 299460431 with hs4 | hs4
          · -- n < 299460431
            rcases Nat.lt_or_ge n 299280575 with hs5 | hs5
            · -- n < 299280575
              exact Brocard.berndt_galway_chunk_1664 n m (by omega) (by omega) h
            · -- n >= 299280575
              exact Brocard.berndt_galway_chunk_1665 n m (by omega) (by omega) h
          · -- n >= 299460431
            exact Brocard.berndt_galway_chunk_1666 n m (by omega) (by omega) h
        · -- n >= 299640287
          rcases Nat.lt_or_ge n 299820143 with hs4 | hs4
          · -- n < 299820143
            exact Brocard.berndt_galway_chunk_1667 n m (by omega) (by omega) h
          · -- n >= 299820143
            exact Brocard.berndt_galway_chunk_1668 n m (by omega) (by omega) h
