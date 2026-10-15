-- Prove2me | solution 1 for Brocard.berndt_galway_group_099
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:16:10.826709+00:00
-- url     : https://prove2.me/submissions/685b7d69-2fca-477c-be3e-0381be769eef

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4543
import Theorems.Thm_Brocard_berndt_galway_chunk_4544
import Theorems.Thm_Brocard_berndt_galway_chunk_4545
import Theorems.Thm_Brocard_berndt_galway_chunk_4546
import Theorems.Thm_Brocard_berndt_galway_chunk_4547
import Theorems.Thm_Brocard_berndt_galway_chunk_4548
import Theorems.Thm_Brocard_berndt_galway_chunk_4549
import Theorems.Thm_Brocard_berndt_galway_chunk_4550
import Theorems.Thm_Brocard_berndt_galway_chunk_4551
import Theorems.Thm_Brocard_berndt_galway_chunk_4552
import Theorems.Thm_Brocard_berndt_galway_chunk_4553
import Theorems.Thm_Brocard_berndt_galway_chunk_4554
import Theorems.Thm_Brocard_berndt_galway_chunk_4555
import Theorems.Thm_Brocard_berndt_galway_chunk_4556
import Theorems.Thm_Brocard_berndt_galway_chunk_4557
import Theorems.Thm_Brocard_berndt_galway_chunk_4558
import Theorems.Thm_Brocard_berndt_galway_chunk_4559
import Theorems.Thm_Brocard_berndt_galway_chunk_4560
import Theorems.Thm_Brocard_berndt_galway_chunk_4561
import Theorems.Thm_Brocard_berndt_galway_chunk_4562
import Theorems.Thm_Brocard_berndt_galway_chunk_4563
import Theorems.Thm_Brocard_berndt_galway_chunk_4564
import Theorems.Thm_Brocard_berndt_galway_chunk_4565
import Theorems.Thm_Brocard_berndt_galway_chunk_4566
import Theorems.Thm_Brocard_berndt_galway_chunk_4567
import Theorems.Thm_Brocard_berndt_galway_chunk_4568
import Theorems.Thm_Brocard_berndt_galway_chunk_4569
import Theorems.Thm_Brocard_berndt_galway_chunk_4570
import Theorems.Thm_Brocard_berndt_galway_chunk_4571
import Theorems.Thm_Brocard_berndt_galway_chunk_4572
import Theorems.Thm_Brocard_berndt_galway_chunk_4573
import Theorems.Thm_Brocard_berndt_galway_chunk_4574
import Theorems.Thm_Brocard_berndt_galway_chunk_4575
import Theorems.Thm_Brocard_berndt_galway_chunk_4576
import Theorems.Thm_Brocard_berndt_galway_chunk_4577
import Theorems.Thm_Brocard_berndt_galway_chunk_4578
import Theorems.Thm_Brocard_berndt_galway_chunk_4579
import Theorems.Thm_Brocard_berndt_galway_chunk_4580
import Theorems.Thm_Brocard_berndt_galway_chunk_4581
import Theorems.Thm_Brocard_berndt_galway_chunk_4582
import Theorems.Thm_Brocard_berndt_galway_chunk_4583
import Theorems.Thm_Brocard_berndt_galway_chunk_4584
import Theorems.Thm_Brocard_berndt_galway_chunk_4585
import Theorems.Thm_Brocard_berndt_galway_chunk_4586
import Theorems.Thm_Brocard_berndt_galway_chunk_4587
import Theorems.Thm_Brocard_berndt_galway_chunk_4588
import Theorems.Thm_Brocard_berndt_galway_chunk_4589

theorem solution (n m : ℕ) (h1 : 816906474 ≤ n) (h2 : n < 825359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 821223021 with hs0 | hs0
  · -- n < 821223021
    rcases Nat.lt_or_ge n 819064748 with hs1 | hs1
    · -- n < 819064748
      rcases Nat.lt_or_ge n 817985611 with hs2 | hs2
      · -- n < 817985611
        rcases Nat.lt_or_ge n 817446043 with hs3 | hs3
        · -- n < 817446043
          rcases Nat.lt_or_ge n 817266187 with hs4 | hs4
          · -- n < 817266187
            rcases Nat.lt_or_ge n 817086330 with hs5 | hs5
            · -- n < 817086330
              exact Brocard.berndt_galway_chunk_4543 n m (by omega) (by omega) h
            · -- n >= 817086330
              exact Brocard.berndt_galway_chunk_4544 n m (by omega) (by omega) h
          · -- n >= 817266187
            exact Brocard.berndt_galway_chunk_4545 n m (by omega) (by omega) h
        · -- n >= 817446043
          rcases Nat.lt_or_ge n 817805755 with hs4 | hs4
          · -- n < 817805755
            rcases Nat.lt_or_ge n 817625899 with hs5 | hs5
            · -- n < 817625899
              exact Brocard.berndt_galway_chunk_4546 n m (by omega) (by omega) h
            · -- n >= 817625899
              exact Brocard.berndt_galway_chunk_4547 n m (by omega) (by omega) h
          · -- n >= 817805755
            exact Brocard.berndt_galway_chunk_4548 n m (by omega) (by omega) h
      · -- n >= 817985611
        rcases Nat.lt_or_ge n 818525179 with hs3 | hs3
        · -- n < 818525179
          rcases Nat.lt_or_ge n 818345323 with hs4 | hs4
          · -- n < 818345323
            rcases Nat.lt_or_ge n 818165467 with hs5 | hs5
            · -- n < 818165467
              exact Brocard.berndt_galway_chunk_4549 n m (by omega) (by omega) h
            · -- n >= 818165467
              exact Brocard.berndt_galway_chunk_4550 n m (by omega) (by omega) h
          · -- n >= 818345323
            exact Brocard.berndt_galway_chunk_4551 n m (by omega) (by omega) h
        · -- n >= 818525179
          rcases Nat.lt_or_ge n 818884892 with hs4 | hs4
          · -- n < 818884892
            rcases Nat.lt_or_ge n 818705035 with hs5 | hs5
            · -- n < 818705035
              exact Brocard.berndt_galway_chunk_4552 n m (by omega) (by omega) h
            · -- n >= 818705035
              exact Brocard.berndt_galway_chunk_4553 n m (by omega) (by omega) h
          · -- n >= 818884892
            exact Brocard.berndt_galway_chunk_4554 n m (by omega) (by omega) h
    · -- n >= 819064748
      rcases Nat.lt_or_ge n 820143884 with hs2 | hs2
      · -- n < 820143884
        rcases Nat.lt_or_ge n 819604316 with hs3 | hs3
        · -- n < 819604316
          rcases Nat.lt_or_ge n 819424460 with hs4 | hs4
          · -- n < 819424460
            rcases Nat.lt_or_ge n 819244604 with hs5 | hs5
            · -- n < 819244604
              exact Brocard.berndt_galway_chunk_4555 n m (by omega) (by omega) h
            · -- n >= 819244604
              exact Brocard.berndt_galway_chunk_4556 n m (by omega) (by omega) h
          · -- n >= 819424460
            exact Brocard.berndt_galway_chunk_4557 n m (by omega) (by omega) h
        · -- n >= 819604316
          rcases Nat.lt_or_ge n 819964028 with hs4 | hs4
          · -- n < 819964028
            rcases Nat.lt_or_ge n 819784172 with hs5 | hs5
            · -- n < 819784172
              exact Brocard.berndt_galway_chunk_4558 n m (by omega) (by omega) h
            · -- n >= 819784172
              exact Brocard.berndt_galway_chunk_4559 n m (by omega) (by omega) h
          · -- n >= 819964028
            exact Brocard.berndt_galway_chunk_4560 n m (by omega) (by omega) h
      · -- n >= 820143884
        rcases Nat.lt_or_ge n 820683453 with hs3 | hs3
        · -- n < 820683453
          rcases Nat.lt_or_ge n 820503597 with hs4 | hs4
          · -- n < 820503597
            rcases Nat.lt_or_ge n 820323741 with hs5 | hs5
            · -- n < 820323741
              exact Brocard.berndt_galway_chunk_4561 n m (by omega) (by omega) h
            · -- n >= 820323741
              exact Brocard.berndt_galway_chunk_4562 n m (by omega) (by omega) h
          · -- n >= 820503597
            exact Brocard.berndt_galway_chunk_4563 n m (by omega) (by omega) h
        · -- n >= 820683453
          rcases Nat.lt_or_ge n 821043165 with hs4 | hs4
          · -- n < 821043165
            rcases Nat.lt_or_ge n 820863309 with hs5 | hs5
            · -- n < 820863309
              exact Brocard.berndt_galway_chunk_4564 n m (by omega) (by omega) h
            · -- n >= 820863309
              exact Brocard.berndt_galway_chunk_4565 n m (by omega) (by omega) h
          · -- n >= 821043165
            exact Brocard.berndt_galway_chunk_4566 n m (by omega) (by omega) h
  · -- n >= 821223021
    rcases Nat.lt_or_ge n 823381294 with hs1 | hs1
    · -- n < 823381294
      rcases Nat.lt_or_ge n 822302158 with hs2 | hs2
      · -- n < 822302158
        rcases Nat.lt_or_ge n 821762589 with hs3 | hs3
        · -- n < 821762589
          rcases Nat.lt_or_ge n 821582733 with hs4 | hs4
          · -- n < 821582733
            rcases Nat.lt_or_ge n 821402877 with hs5 | hs5
            · -- n < 821402877
              exact Brocard.berndt_galway_chunk_4567 n m (by omega) (by omega) h
            · -- n >= 821402877
              exact Brocard.berndt_galway_chunk_4568 n m (by omega) (by omega) h
          · -- n >= 821582733
            exact Brocard.berndt_galway_chunk_4569 n m (by omega) (by omega) h
        · -- n >= 821762589
          rcases Nat.lt_or_ge n 822122302 with hs4 | hs4
          · -- n < 822122302
            rcases Nat.lt_or_ge n 821942446 with hs5 | hs5
            · -- n < 821942446
              exact Brocard.berndt_galway_chunk_4570 n m (by omega) (by omega) h
            · -- n >= 821942446
              exact Brocard.berndt_galway_chunk_4571 n m (by omega) (by omega) h
          · -- n >= 822122302
            exact Brocard.berndt_galway_chunk_4572 n m (by omega) (by omega) h
      · -- n >= 822302158
        rcases Nat.lt_or_ge n 822841726 with hs3 | hs3
        · -- n < 822841726
          rcases Nat.lt_or_ge n 822661870 with hs4 | hs4
          · -- n < 822661870
            rcases Nat.lt_or_ge n 822482014 with hs5 | hs5
            · -- n < 822482014
              exact Brocard.berndt_galway_chunk_4573 n m (by omega) (by omega) h
            · -- n >= 822482014
              exact Brocard.berndt_galway_chunk_4574 n m (by omega) (by omega) h
          · -- n >= 822661870
            exact Brocard.berndt_galway_chunk_4575 n m (by omega) (by omega) h
        · -- n >= 822841726
          rcases Nat.lt_or_ge n 823201438 with hs4 | hs4
          · -- n < 823201438
            rcases Nat.lt_or_ge n 823021582 with hs5 | hs5
            · -- n < 823021582
              exact Brocard.berndt_galway_chunk_4576 n m (by omega) (by omega) h
            · -- n >= 823021582
              exact Brocard.berndt_galway_chunk_4577 n m (by omega) (by omega) h
          · -- n >= 823201438
            exact Brocard.berndt_galway_chunk_4578 n m (by omega) (by omega) h
    · -- n >= 823381294
      rcases Nat.lt_or_ge n 824460431 with hs2 | hs2
      · -- n < 824460431
        rcases Nat.lt_or_ge n 823920863 with hs3 | hs3
        · -- n < 823920863
          rcases Nat.lt_or_ge n 823741007 with hs4 | hs4
          · -- n < 823741007
            rcases Nat.lt_or_ge n 823561151 with hs5 | hs5
            · -- n < 823561151
              exact Brocard.berndt_galway_chunk_4579 n m (by omega) (by omega) h
            · -- n >= 823561151
              exact Brocard.berndt_galway_chunk_4580 n m (by omega) (by omega) h
          · -- n >= 823741007
            exact Brocard.berndt_galway_chunk_4581 n m (by omega) (by omega) h
        · -- n >= 823920863
          rcases Nat.lt_or_ge n 824280575 with hs4 | hs4
          · -- n < 824280575
            rcases Nat.lt_or_ge n 824100719 with hs5 | hs5
            · -- n < 824100719
              exact Brocard.berndt_galway_chunk_4582 n m (by omega) (by omega) h
            · -- n >= 824100719
              exact Brocard.berndt_galway_chunk_4583 n m (by omega) (by omega) h
          · -- n >= 824280575
            exact Brocard.berndt_galway_chunk_4584 n m (by omega) (by omega) h
      · -- n >= 824460431
        rcases Nat.lt_or_ge n 825000000 with hs3 | hs3
        · -- n < 825000000
          rcases Nat.lt_or_ge n 824820143 with hs4 | hs4
          · -- n < 824820143
            rcases Nat.lt_or_ge n 824640287 with hs5 | hs5
            · -- n < 824640287
              exact Brocard.berndt_galway_chunk_4585 n m (by omega) (by omega) h
            · -- n >= 824640287
              exact Brocard.berndt_galway_chunk_4586 n m (by omega) (by omega) h
          · -- n >= 824820143
            exact Brocard.berndt_galway_chunk_4587 n m (by omega) (by omega) h
        · -- n >= 825000000
          rcases Nat.lt_or_ge n 825179856 with hs4 | hs4
          · -- n < 825179856
            exact Brocard.berndt_galway_chunk_4588 n m (by omega) (by omega) h
          · -- n >= 825179856
            exact Brocard.berndt_galway_chunk_4589 n m (by omega) (by omega) h
