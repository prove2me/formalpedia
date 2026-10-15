-- Prove2me | solution 1 for Brocard.berndt_galway_group_120
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:27:14.064982+00:00
-- url     : https://prove2.me/submissions/527dfbc4-7cf1-4d25-b74e-1d4e938eddba

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5515
import Theorems.Thm_Brocard_berndt_galway_chunk_5516
import Theorems.Thm_Brocard_berndt_galway_chunk_5517
import Theorems.Thm_Brocard_berndt_galway_chunk_5518
import Theorems.Thm_Brocard_berndt_galway_chunk_5519
import Theorems.Thm_Brocard_berndt_galway_chunk_5520
import Theorems.Thm_Brocard_berndt_galway_chunk_5521
import Theorems.Thm_Brocard_berndt_galway_chunk_5522
import Theorems.Thm_Brocard_berndt_galway_chunk_5523
import Theorems.Thm_Brocard_berndt_galway_chunk_5524
import Theorems.Thm_Brocard_berndt_galway_chunk_5525
import Theorems.Thm_Brocard_berndt_galway_chunk_5526
import Theorems.Thm_Brocard_berndt_galway_chunk_5527
import Theorems.Thm_Brocard_berndt_galway_chunk_5528
import Theorems.Thm_Brocard_berndt_galway_chunk_5529
import Theorems.Thm_Brocard_berndt_galway_chunk_5530
import Theorems.Thm_Brocard_berndt_galway_chunk_5531
import Theorems.Thm_Brocard_berndt_galway_chunk_5532
import Theorems.Thm_Brocard_berndt_galway_chunk_5533
import Theorems.Thm_Brocard_berndt_galway_chunk_5534
import Theorems.Thm_Brocard_berndt_galway_chunk_5535
import Theorems.Thm_Brocard_berndt_galway_chunk_5536
import Theorems.Thm_Brocard_berndt_galway_chunk_5537
import Theorems.Thm_Brocard_berndt_galway_chunk_5538
import Theorems.Thm_Brocard_berndt_galway_chunk_5539
import Theorems.Thm_Brocard_berndt_galway_chunk_5540
import Theorems.Thm_Brocard_berndt_galway_chunk_5541
import Theorems.Thm_Brocard_berndt_galway_chunk_5542
import Theorems.Thm_Brocard_berndt_galway_chunk_5543
import Theorems.Thm_Brocard_berndt_galway_chunk_5544
import Theorems.Thm_Brocard_berndt_galway_chunk_5545
import Theorems.Thm_Brocard_berndt_galway_chunk_5546
import Theorems.Thm_Brocard_berndt_galway_chunk_5547
import Theorems.Thm_Brocard_berndt_galway_chunk_5548
import Theorems.Thm_Brocard_berndt_galway_chunk_5549
import Theorems.Thm_Brocard_berndt_galway_chunk_5550
import Theorems.Thm_Brocard_berndt_galway_chunk_5551
import Theorems.Thm_Brocard_berndt_galway_chunk_5552
import Theorems.Thm_Brocard_berndt_galway_chunk_5553
import Theorems.Thm_Brocard_berndt_galway_chunk_5554
import Theorems.Thm_Brocard_berndt_galway_chunk_5555
import Theorems.Thm_Brocard_berndt_galway_chunk_5556
import Theorems.Thm_Brocard_berndt_galway_chunk_5557
import Theorems.Thm_Brocard_berndt_galway_chunk_5558
import Theorems.Thm_Brocard_berndt_galway_chunk_5559
import Theorems.Thm_Brocard_berndt_galway_chunk_5560

theorem solution (n m : ℕ) (h1 : 991726618 ≤ n) (h2 : n < 1000000000) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 995863309 with hs0 | hs0
  · -- n < 995863309
    rcases Nat.lt_or_ge n 993884892 with hs1 | hs1
    · -- n < 993884892
      rcases Nat.lt_or_ge n 992805755 with hs2 | hs2
      · -- n < 992805755
        rcases Nat.lt_or_ge n 992266187 with hs3 | hs3
        · -- n < 992266187
          rcases Nat.lt_or_ge n 992086330 with hs4 | hs4
          · -- n < 992086330
            rcases Nat.lt_or_ge n 991906474 with hs5 | hs5
            · -- n < 991906474
              exact Brocard.berndt_galway_chunk_5515 n m (by omega) (by omega) h
            · -- n >= 991906474
              exact Brocard.berndt_galway_chunk_5516 n m (by omega) (by omega) h
          · -- n >= 992086330
            exact Brocard.berndt_galway_chunk_5517 n m (by omega) (by omega) h
        · -- n >= 992266187
          rcases Nat.lt_or_ge n 992625899 with hs4 | hs4
          · -- n < 992625899
            rcases Nat.lt_or_ge n 992446043 with hs5 | hs5
            · -- n < 992446043
              exact Brocard.berndt_galway_chunk_5518 n m (by omega) (by omega) h
            · -- n >= 992446043
              exact Brocard.berndt_galway_chunk_5519 n m (by omega) (by omega) h
          · -- n >= 992625899
            exact Brocard.berndt_galway_chunk_5520 n m (by omega) (by omega) h
      · -- n >= 992805755
        rcases Nat.lt_or_ge n 993345323 with hs3 | hs3
        · -- n < 993345323
          rcases Nat.lt_or_ge n 993165467 with hs4 | hs4
          · -- n < 993165467
            rcases Nat.lt_or_ge n 992985611 with hs5 | hs5
            · -- n < 992985611
              exact Brocard.berndt_galway_chunk_5521 n m (by omega) (by omega) h
            · -- n >= 992985611
              exact Brocard.berndt_galway_chunk_5522 n m (by omega) (by omega) h
          · -- n >= 993165467
            exact Brocard.berndt_galway_chunk_5523 n m (by omega) (by omega) h
        · -- n >= 993345323
          rcases Nat.lt_or_ge n 993705035 with hs4 | hs4
          · -- n < 993705035
            rcases Nat.lt_or_ge n 993525179 with hs5 | hs5
            · -- n < 993525179
              exact Brocard.berndt_galway_chunk_5524 n m (by omega) (by omega) h
            · -- n >= 993525179
              exact Brocard.berndt_galway_chunk_5525 n m (by omega) (by omega) h
          · -- n >= 993705035
            exact Brocard.berndt_galway_chunk_5526 n m (by omega) (by omega) h
    · -- n >= 993884892
      rcases Nat.lt_or_ge n 994964028 with hs2 | hs2
      · -- n < 994964028
        rcases Nat.lt_or_ge n 994424460 with hs3 | hs3
        · -- n < 994424460
          rcases Nat.lt_or_ge n 994244604 with hs4 | hs4
          · -- n < 994244604
            rcases Nat.lt_or_ge n 994064748 with hs5 | hs5
            · -- n < 994064748
              exact Brocard.berndt_galway_chunk_5527 n m (by omega) (by omega) h
            · -- n >= 994064748
              exact Brocard.berndt_galway_chunk_5528 n m (by omega) (by omega) h
          · -- n >= 994244604
            exact Brocard.berndt_galway_chunk_5529 n m (by omega) (by omega) h
        · -- n >= 994424460
          rcases Nat.lt_or_ge n 994784172 with hs4 | hs4
          · -- n < 994784172
            rcases Nat.lt_or_ge n 994604316 with hs5 | hs5
            · -- n < 994604316
              exact Brocard.berndt_galway_chunk_5530 n m (by omega) (by omega) h
            · -- n >= 994604316
              exact Brocard.berndt_galway_chunk_5531 n m (by omega) (by omega) h
          · -- n >= 994784172
            exact Brocard.berndt_galway_chunk_5532 n m (by omega) (by omega) h
      · -- n >= 994964028
        rcases Nat.lt_or_ge n 995503597 with hs3 | hs3
        · -- n < 995503597
          rcases Nat.lt_or_ge n 995323741 with hs4 | hs4
          · -- n < 995323741
            rcases Nat.lt_or_ge n 995143884 with hs5 | hs5
            · -- n < 995143884
              exact Brocard.berndt_galway_chunk_5533 n m (by omega) (by omega) h
            · -- n >= 995143884
              exact Brocard.berndt_galway_chunk_5534 n m (by omega) (by omega) h
          · -- n >= 995323741
            exact Brocard.berndt_galway_chunk_5535 n m (by omega) (by omega) h
        · -- n >= 995503597
          rcases Nat.lt_or_ge n 995683453 with hs4 | hs4
          · -- n < 995683453
            exact Brocard.berndt_galway_chunk_5536 n m (by omega) (by omega) h
          · -- n >= 995683453
            exact Brocard.berndt_galway_chunk_5537 n m (by omega) (by omega) h
  · -- n >= 995863309
    rcases Nat.lt_or_ge n 998021582 with hs1 | hs1
    · -- n < 998021582
      rcases Nat.lt_or_ge n 996942446 with hs2 | hs2
      · -- n < 996942446
        rcases Nat.lt_or_ge n 996402877 with hs3 | hs3
        · -- n < 996402877
          rcases Nat.lt_or_ge n 996223021 with hs4 | hs4
          · -- n < 996223021
            rcases Nat.lt_or_ge n 996043165 with hs5 | hs5
            · -- n < 996043165
              exact Brocard.berndt_galway_chunk_5538 n m (by omega) (by omega) h
            · -- n >= 996043165
              exact Brocard.berndt_galway_chunk_5539 n m (by omega) (by omega) h
          · -- n >= 996223021
            exact Brocard.berndt_galway_chunk_5540 n m (by omega) (by omega) h
        · -- n >= 996402877
          rcases Nat.lt_or_ge n 996762589 with hs4 | hs4
          · -- n < 996762589
            rcases Nat.lt_or_ge n 996582733 with hs5 | hs5
            · -- n < 996582733
              exact Brocard.berndt_galway_chunk_5541 n m (by omega) (by omega) h
            · -- n >= 996582733
              exact Brocard.berndt_galway_chunk_5542 n m (by omega) (by omega) h
          · -- n >= 996762589
            exact Brocard.berndt_galway_chunk_5543 n m (by omega) (by omega) h
      · -- n >= 996942446
        rcases Nat.lt_or_ge n 997482014 with hs3 | hs3
        · -- n < 997482014
          rcases Nat.lt_or_ge n 997302158 with hs4 | hs4
          · -- n < 997302158
            rcases Nat.lt_or_ge n 997122302 with hs5 | hs5
            · -- n < 997122302
              exact Brocard.berndt_galway_chunk_5544 n m (by omega) (by omega) h
            · -- n >= 997122302
              exact Brocard.berndt_galway_chunk_5545 n m (by omega) (by omega) h
          · -- n >= 997302158
            exact Brocard.berndt_galway_chunk_5546 n m (by omega) (by omega) h
        · -- n >= 997482014
          rcases Nat.lt_or_ge n 997841726 with hs4 | hs4
          · -- n < 997841726
            rcases Nat.lt_or_ge n 997661870 with hs5 | hs5
            · -- n < 997661870
              exact Brocard.berndt_galway_chunk_5547 n m (by omega) (by omega) h
            · -- n >= 997661870
              exact Brocard.berndt_galway_chunk_5548 n m (by omega) (by omega) h
          · -- n >= 997841726
            exact Brocard.berndt_galway_chunk_5549 n m (by omega) (by omega) h
    · -- n >= 998021582
      rcases Nat.lt_or_ge n 999100719 with hs2 | hs2
      · -- n < 999100719
        rcases Nat.lt_or_ge n 998561151 with hs3 | hs3
        · -- n < 998561151
          rcases Nat.lt_or_ge n 998381294 with hs4 | hs4
          · -- n < 998381294
            rcases Nat.lt_or_ge n 998201438 with hs5 | hs5
            · -- n < 998201438
              exact Brocard.berndt_galway_chunk_5550 n m (by omega) (by omega) h
            · -- n >= 998201438
              exact Brocard.berndt_galway_chunk_5551 n m (by omega) (by omega) h
          · -- n >= 998381294
            exact Brocard.berndt_galway_chunk_5552 n m (by omega) (by omega) h
        · -- n >= 998561151
          rcases Nat.lt_or_ge n 998920863 with hs4 | hs4
          · -- n < 998920863
            rcases Nat.lt_or_ge n 998741007 with hs5 | hs5
            · -- n < 998741007
              exact Brocard.berndt_galway_chunk_5553 n m (by omega) (by omega) h
            · -- n >= 998741007
              exact Brocard.berndt_galway_chunk_5554 n m (by omega) (by omega) h
          · -- n >= 998920863
            exact Brocard.berndt_galway_chunk_5555 n m (by omega) (by omega) h
      · -- n >= 999100719
        rcases Nat.lt_or_ge n 999640287 with hs3 | hs3
        · -- n < 999640287
          rcases Nat.lt_or_ge n 999460431 with hs4 | hs4
          · -- n < 999460431
            rcases Nat.lt_or_ge n 999280575 with hs5 | hs5
            · -- n < 999280575
              exact Brocard.berndt_galway_chunk_5556 n m (by omega) (by omega) h
            · -- n >= 999280575
              exact Brocard.berndt_galway_chunk_5557 n m (by omega) (by omega) h
          · -- n >= 999460431
            exact Brocard.berndt_galway_chunk_5558 n m (by omega) (by omega) h
        · -- n >= 999640287
          rcases Nat.lt_or_ge n 999820143 with hs4 | hs4
          · -- n < 999820143
            exact Brocard.berndt_galway_chunk_5559 n m (by omega) (by omega) h
          · -- n >= 999820143
            exact Brocard.berndt_galway_chunk_5560 n m (by omega) (by omega) h
