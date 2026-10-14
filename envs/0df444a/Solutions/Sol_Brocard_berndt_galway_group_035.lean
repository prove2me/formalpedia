-- Prove2me | solution 1 for Brocard.berndt_galway_group_035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:09:55.655533+00:00
-- url     : https://prove2.me/submissions/52f0c630-9786-4217-a6c6-c357ac8d84d2

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_1577
import Theorems.Thm_Brocard_berndt_galway_chunk_1578
import Theorems.Thm_Brocard_berndt_galway_chunk_1579
import Theorems.Thm_Brocard_berndt_galway_chunk_1580
import Theorems.Thm_Brocard_berndt_galway_chunk_1581
import Theorems.Thm_Brocard_berndt_galway_chunk_1582
import Theorems.Thm_Brocard_berndt_galway_chunk_1583
import Theorems.Thm_Brocard_berndt_galway_chunk_1584
import Theorems.Thm_Brocard_berndt_galway_chunk_1585
import Theorems.Thm_Brocard_berndt_galway_chunk_1586
import Theorems.Thm_Brocard_berndt_galway_chunk_1587
import Theorems.Thm_Brocard_berndt_galway_chunk_1588
import Theorems.Thm_Brocard_berndt_galway_chunk_1589
import Theorems.Thm_Brocard_berndt_galway_chunk_1590
import Theorems.Thm_Brocard_berndt_galway_chunk_1591
import Theorems.Thm_Brocard_berndt_galway_chunk_1592
import Theorems.Thm_Brocard_berndt_galway_chunk_1593
import Theorems.Thm_Brocard_berndt_galway_chunk_1594
import Theorems.Thm_Brocard_berndt_galway_chunk_1595
import Theorems.Thm_Brocard_berndt_galway_chunk_1596
import Theorems.Thm_Brocard_berndt_galway_chunk_1597
import Theorems.Thm_Brocard_berndt_galway_chunk_1598
import Theorems.Thm_Brocard_berndt_galway_chunk_1599
import Theorems.Thm_Brocard_berndt_galway_chunk_1600
import Theorems.Thm_Brocard_berndt_galway_chunk_1601
import Theorems.Thm_Brocard_berndt_galway_chunk_1602
import Theorems.Thm_Brocard_berndt_galway_chunk_1603
import Theorems.Thm_Brocard_berndt_galway_chunk_1604
import Theorems.Thm_Brocard_berndt_galway_chunk_1605
import Theorems.Thm_Brocard_berndt_galway_chunk_1606
import Theorems.Thm_Brocard_berndt_galway_chunk_1607
import Theorems.Thm_Brocard_berndt_galway_chunk_1608
import Theorems.Thm_Brocard_berndt_galway_chunk_1609
import Theorems.Thm_Brocard_berndt_galway_chunk_1610
import Theorems.Thm_Brocard_berndt_galway_chunk_1611
import Theorems.Thm_Brocard_berndt_galway_chunk_1612
import Theorems.Thm_Brocard_berndt_galway_chunk_1613
import Theorems.Thm_Brocard_berndt_galway_chunk_1614
import Theorems.Thm_Brocard_berndt_galway_chunk_1615
import Theorems.Thm_Brocard_berndt_galway_chunk_1616
import Theorems.Thm_Brocard_berndt_galway_chunk_1617
import Theorems.Thm_Brocard_berndt_galway_chunk_1618
import Theorems.Thm_Brocard_berndt_galway_chunk_1619
import Theorems.Thm_Brocard_berndt_galway_chunk_1620
import Theorems.Thm_Brocard_berndt_galway_chunk_1621
import Theorems.Thm_Brocard_berndt_galway_chunk_1622

theorem solution (n m : ℕ) (h1 : 283453237 ≤ n) (h2 : n < 291726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 287589928 with hs0 | hs0
  · -- n < 287589928
    rcases Nat.lt_or_ge n 285611510 with hs1 | hs1
    · -- n < 285611510
      rcases Nat.lt_or_ge n 284532374 with hs2 | hs2
      · -- n < 284532374
        rcases Nat.lt_or_ge n 283992805 with hs3 | hs3
        · -- n < 283992805
          rcases Nat.lt_or_ge n 283812949 with hs4 | hs4
          · -- n < 283812949
            rcases Nat.lt_or_ge n 283633093 with hs5 | hs5
            · -- n < 283633093
              exact Brocard.berndt_galway_chunk_1577 n m (by omega) (by omega) h
            · -- n >= 283633093
              exact Brocard.berndt_galway_chunk_1578 n m (by omega) (by omega) h
          · -- n >= 283812949
            exact Brocard.berndt_galway_chunk_1579 n m (by omega) (by omega) h
        · -- n >= 283992805
          rcases Nat.lt_or_ge n 284352517 with hs4 | hs4
          · -- n < 284352517
            rcases Nat.lt_or_ge n 284172661 with hs5 | hs5
            · -- n < 284172661
              exact Brocard.berndt_galway_chunk_1580 n m (by omega) (by omega) h
            · -- n >= 284172661
              exact Brocard.berndt_galway_chunk_1581 n m (by omega) (by omega) h
          · -- n >= 284352517
            exact Brocard.berndt_galway_chunk_1582 n m (by omega) (by omega) h
      · -- n >= 284532374
        rcases Nat.lt_or_ge n 285071942 with hs3 | hs3
        · -- n < 285071942
          rcases Nat.lt_or_ge n 284892086 with hs4 | hs4
          · -- n < 284892086
            rcases Nat.lt_or_ge n 284712230 with hs5 | hs5
            · -- n < 284712230
              exact Brocard.berndt_galway_chunk_1583 n m (by omega) (by omega) h
            · -- n >= 284712230
              exact Brocard.berndt_galway_chunk_1584 n m (by omega) (by omega) h
          · -- n >= 284892086
            exact Brocard.berndt_galway_chunk_1585 n m (by omega) (by omega) h
        · -- n >= 285071942
          rcases Nat.lt_or_ge n 285431654 with hs4 | hs4
          · -- n < 285431654
            rcases Nat.lt_or_ge n 285251798 with hs5 | hs5
            · -- n < 285251798
              exact Brocard.berndt_galway_chunk_1586 n m (by omega) (by omega) h
            · -- n >= 285251798
              exact Brocard.berndt_galway_chunk_1587 n m (by omega) (by omega) h
          · -- n >= 285431654
            exact Brocard.berndt_galway_chunk_1588 n m (by omega) (by omega) h
    · -- n >= 285611510
      rcases Nat.lt_or_ge n 286690647 with hs2 | hs2
      · -- n < 286690647
        rcases Nat.lt_or_ge n 286151079 with hs3 | hs3
        · -- n < 286151079
          rcases Nat.lt_or_ge n 285971223 with hs4 | hs4
          · -- n < 285971223
            rcases Nat.lt_or_ge n 285791366 with hs5 | hs5
            · -- n < 285791366
              exact Brocard.berndt_galway_chunk_1589 n m (by omega) (by omega) h
            · -- n >= 285791366
              exact Brocard.berndt_galway_chunk_1590 n m (by omega) (by omega) h
          · -- n >= 285971223
            exact Brocard.berndt_galway_chunk_1591 n m (by omega) (by omega) h
        · -- n >= 286151079
          rcases Nat.lt_or_ge n 286510791 with hs4 | hs4
          · -- n < 286510791
            rcases Nat.lt_or_ge n 286330935 with hs5 | hs5
            · -- n < 286330935
              exact Brocard.berndt_galway_chunk_1592 n m (by omega) (by omega) h
            · -- n >= 286330935
              exact Brocard.berndt_galway_chunk_1593 n m (by omega) (by omega) h
          · -- n >= 286510791
            exact Brocard.berndt_galway_chunk_1594 n m (by omega) (by omega) h
      · -- n >= 286690647
        rcases Nat.lt_or_ge n 287230215 with hs3 | hs3
        · -- n < 287230215
          rcases Nat.lt_or_ge n 287050359 with hs4 | hs4
          · -- n < 287050359
            rcases Nat.lt_or_ge n 286870503 with hs5 | hs5
            · -- n < 286870503
              exact Brocard.berndt_galway_chunk_1595 n m (by omega) (by omega) h
            · -- n >= 286870503
              exact Brocard.berndt_galway_chunk_1596 n m (by omega) (by omega) h
          · -- n >= 287050359
            exact Brocard.berndt_galway_chunk_1597 n m (by omega) (by omega) h
        · -- n >= 287230215
          rcases Nat.lt_or_ge n 287410071 with hs4 | hs4
          · -- n < 287410071
            exact Brocard.berndt_galway_chunk_1598 n m (by omega) (by omega) h
          · -- n >= 287410071
            exact Brocard.berndt_galway_chunk_1599 n m (by omega) (by omega) h
  · -- n >= 287589928
    rcases Nat.lt_or_ge n 289748201 with hs1 | hs1
    · -- n < 289748201
      rcases Nat.lt_or_ge n 288669064 with hs2 | hs2
      · -- n < 288669064
        rcases Nat.lt_or_ge n 288129496 with hs3 | hs3
        · -- n < 288129496
          rcases Nat.lt_or_ge n 287949640 with hs4 | hs4
          · -- n < 287949640
            rcases Nat.lt_or_ge n 287769784 with hs5 | hs5
            · -- n < 287769784
              exact Brocard.berndt_galway_chunk_1600 n m (by omega) (by omega) h
            · -- n >= 287769784
              exact Brocard.berndt_galway_chunk_1601 n m (by omega) (by omega) h
          · -- n >= 287949640
            exact Brocard.berndt_galway_chunk_1602 n m (by omega) (by omega) h
        · -- n >= 288129496
          rcases Nat.lt_or_ge n 288489208 with hs4 | hs4
          · -- n < 288489208
            rcases Nat.lt_or_ge n 288309352 with hs5 | hs5
            · -- n < 288309352
              exact Brocard.berndt_galway_chunk_1603 n m (by omega) (by omega) h
            · -- n >= 288309352
              exact Brocard.berndt_galway_chunk_1604 n m (by omega) (by omega) h
          · -- n >= 288489208
            exact Brocard.berndt_galway_chunk_1605 n m (by omega) (by omega) h
      · -- n >= 288669064
        rcases Nat.lt_or_ge n 289208633 with hs3 | hs3
        · -- n < 289208633
          rcases Nat.lt_or_ge n 289028776 with hs4 | hs4
          · -- n < 289028776
            rcases Nat.lt_or_ge n 288848920 with hs5 | hs5
            · -- n < 288848920
              exact Brocard.berndt_galway_chunk_1606 n m (by omega) (by omega) h
            · -- n >= 288848920
              exact Brocard.berndt_galway_chunk_1607 n m (by omega) (by omega) h
          · -- n >= 289028776
            exact Brocard.berndt_galway_chunk_1608 n m (by omega) (by omega) h
        · -- n >= 289208633
          rcases Nat.lt_or_ge n 289568345 with hs4 | hs4
          · -- n < 289568345
            rcases Nat.lt_or_ge n 289388489 with hs5 | hs5
            · -- n < 289388489
              exact Brocard.berndt_galway_chunk_1609 n m (by omega) (by omega) h
            · -- n >= 289388489
              exact Brocard.berndt_galway_chunk_1610 n m (by omega) (by omega) h
          · -- n >= 289568345
            exact Brocard.berndt_galway_chunk_1611 n m (by omega) (by omega) h
    · -- n >= 289748201
      rcases Nat.lt_or_ge n 290827338 with hs2 | hs2
      · -- n < 290827338
        rcases Nat.lt_or_ge n 290287769 with hs3 | hs3
        · -- n < 290287769
          rcases Nat.lt_or_ge n 290107913 with hs4 | hs4
          · -- n < 290107913
            rcases Nat.lt_or_ge n 289928057 with hs5 | hs5
            · -- n < 289928057
              exact Brocard.berndt_galway_chunk_1612 n m (by omega) (by omega) h
            · -- n >= 289928057
              exact Brocard.berndt_galway_chunk_1613 n m (by omega) (by omega) h
          · -- n >= 290107913
            exact Brocard.berndt_galway_chunk_1614 n m (by omega) (by omega) h
        · -- n >= 290287769
          rcases Nat.lt_or_ge n 290647482 with hs4 | hs4
          · -- n < 290647482
            rcases Nat.lt_or_ge n 290467625 with hs5 | hs5
            · -- n < 290467625
              exact Brocard.berndt_galway_chunk_1615 n m (by omega) (by omega) h
            · -- n >= 290467625
              exact Brocard.berndt_galway_chunk_1616 n m (by omega) (by omega) h
          · -- n >= 290647482
            exact Brocard.berndt_galway_chunk_1617 n m (by omega) (by omega) h
      · -- n >= 290827338
        rcases Nat.lt_or_ge n 291366906 with hs3 | hs3
        · -- n < 291366906
          rcases Nat.lt_or_ge n 291187050 with hs4 | hs4
          · -- n < 291187050
            rcases Nat.lt_or_ge n 291007194 with hs5 | hs5
            · -- n < 291007194
              exact Brocard.berndt_galway_chunk_1618 n m (by omega) (by omega) h
            · -- n >= 291007194
              exact Brocard.berndt_galway_chunk_1619 n m (by omega) (by omega) h
          · -- n >= 291187050
            exact Brocard.berndt_galway_chunk_1620 n m (by omega) (by omega) h
        · -- n >= 291366906
          rcases Nat.lt_or_ge n 291546762 with hs4 | hs4
          · -- n < 291546762
            exact Brocard.berndt_galway_chunk_1621 n m (by omega) (by omega) h
          · -- n >= 291546762
            exact Brocard.berndt_galway_chunk_1622 n m (by omega) (by omega) h
