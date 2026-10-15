-- Prove2me | solution 1 for Brocard.berndt_galway_group_093
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:19:05.599383+00:00
-- url     : https://prove2.me/submissions/7446ddec-f3e8-4d17-a2c1-2f8a43f05670

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4265
import Theorems.Thm_Brocard_berndt_galway_chunk_4266
import Theorems.Thm_Brocard_berndt_galway_chunk_4267
import Theorems.Thm_Brocard_berndt_galway_chunk_4268
import Theorems.Thm_Brocard_berndt_galway_chunk_4269
import Theorems.Thm_Brocard_berndt_galway_chunk_4270
import Theorems.Thm_Brocard_berndt_galway_chunk_4271
import Theorems.Thm_Brocard_berndt_galway_chunk_4272
import Theorems.Thm_Brocard_berndt_galway_chunk_4273
import Theorems.Thm_Brocard_berndt_galway_chunk_4274
import Theorems.Thm_Brocard_berndt_galway_chunk_4275
import Theorems.Thm_Brocard_berndt_galway_chunk_4276
import Theorems.Thm_Brocard_berndt_galway_chunk_4277
import Theorems.Thm_Brocard_berndt_galway_chunk_4278
import Theorems.Thm_Brocard_berndt_galway_chunk_4279
import Theorems.Thm_Brocard_berndt_galway_chunk_4280
import Theorems.Thm_Brocard_berndt_galway_chunk_4281
import Theorems.Thm_Brocard_berndt_galway_chunk_4282
import Theorems.Thm_Brocard_berndt_galway_chunk_4283
import Theorems.Thm_Brocard_berndt_galway_chunk_4284
import Theorems.Thm_Brocard_berndt_galway_chunk_4285
import Theorems.Thm_Brocard_berndt_galway_chunk_4286
import Theorems.Thm_Brocard_berndt_galway_chunk_4287
import Theorems.Thm_Brocard_berndt_galway_chunk_4288
import Theorems.Thm_Brocard_berndt_galway_chunk_4289
import Theorems.Thm_Brocard_berndt_galway_chunk_4290
import Theorems.Thm_Brocard_berndt_galway_chunk_4291
import Theorems.Thm_Brocard_berndt_galway_chunk_4292
import Theorems.Thm_Brocard_berndt_galway_chunk_4293
import Theorems.Thm_Brocard_berndt_galway_chunk_4294
import Theorems.Thm_Brocard_berndt_galway_chunk_4295
import Theorems.Thm_Brocard_berndt_galway_chunk_4296
import Theorems.Thm_Brocard_berndt_galway_chunk_4297
import Theorems.Thm_Brocard_berndt_galway_chunk_4298
import Theorems.Thm_Brocard_berndt_galway_chunk_4299
import Theorems.Thm_Brocard_berndt_galway_chunk_4300
import Theorems.Thm_Brocard_berndt_galway_chunk_4301
import Theorems.Thm_Brocard_berndt_galway_chunk_4302
import Theorems.Thm_Brocard_berndt_galway_chunk_4303
import Theorems.Thm_Brocard_berndt_galway_chunk_4304
import Theorems.Thm_Brocard_berndt_galway_chunk_4305
import Theorems.Thm_Brocard_berndt_galway_chunk_4306
import Theorems.Thm_Brocard_berndt_galway_chunk_4307
import Theorems.Thm_Brocard_berndt_galway_chunk_4308
import Theorems.Thm_Brocard_berndt_galway_chunk_4309
import Theorems.Thm_Brocard_berndt_galway_chunk_4310

theorem solution (n m : ℕ) (h1 : 766906474 ≤ n) (h2 : n < 775179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 771043165 with hs0 | hs0
  · -- n < 771043165
    rcases Nat.lt_or_ge n 769064748 with hs1 | hs1
    · -- n < 769064748
      rcases Nat.lt_or_ge n 767985611 with hs2 | hs2
      · -- n < 767985611
        rcases Nat.lt_or_ge n 767446043 with hs3 | hs3
        · -- n < 767446043
          rcases Nat.lt_or_ge n 767266187 with hs4 | hs4
          · -- n < 767266187
            rcases Nat.lt_or_ge n 767086330 with hs5 | hs5
            · -- n < 767086330
              exact Brocard.berndt_galway_chunk_4265 n m (by omega) (by omega) h
            · -- n >= 767086330
              exact Brocard.berndt_galway_chunk_4266 n m (by omega) (by omega) h
          · -- n >= 767266187
            exact Brocard.berndt_galway_chunk_4267 n m (by omega) (by omega) h
        · -- n >= 767446043
          rcases Nat.lt_or_ge n 767805755 with hs4 | hs4
          · -- n < 767805755
            rcases Nat.lt_or_ge n 767625899 with hs5 | hs5
            · -- n < 767625899
              exact Brocard.berndt_galway_chunk_4268 n m (by omega) (by omega) h
            · -- n >= 767625899
              exact Brocard.berndt_galway_chunk_4269 n m (by omega) (by omega) h
          · -- n >= 767805755
            exact Brocard.berndt_galway_chunk_4270 n m (by omega) (by omega) h
      · -- n >= 767985611
        rcases Nat.lt_or_ge n 768525179 with hs3 | hs3
        · -- n < 768525179
          rcases Nat.lt_or_ge n 768345323 with hs4 | hs4
          · -- n < 768345323
            rcases Nat.lt_or_ge n 768165467 with hs5 | hs5
            · -- n < 768165467
              exact Brocard.berndt_galway_chunk_4271 n m (by omega) (by omega) h
            · -- n >= 768165467
              exact Brocard.berndt_galway_chunk_4272 n m (by omega) (by omega) h
          · -- n >= 768345323
            exact Brocard.berndt_galway_chunk_4273 n m (by omega) (by omega) h
        · -- n >= 768525179
          rcases Nat.lt_or_ge n 768884892 with hs4 | hs4
          · -- n < 768884892
            rcases Nat.lt_or_ge n 768705035 with hs5 | hs5
            · -- n < 768705035
              exact Brocard.berndt_galway_chunk_4274 n m (by omega) (by omega) h
            · -- n >= 768705035
              exact Brocard.berndt_galway_chunk_4275 n m (by omega) (by omega) h
          · -- n >= 768884892
            exact Brocard.berndt_galway_chunk_4276 n m (by omega) (by omega) h
    · -- n >= 769064748
      rcases Nat.lt_or_ge n 770143884 with hs2 | hs2
      · -- n < 770143884
        rcases Nat.lt_or_ge n 769604316 with hs3 | hs3
        · -- n < 769604316
          rcases Nat.lt_or_ge n 769424460 with hs4 | hs4
          · -- n < 769424460
            rcases Nat.lt_or_ge n 769244604 with hs5 | hs5
            · -- n < 769244604
              exact Brocard.berndt_galway_chunk_4277 n m (by omega) (by omega) h
            · -- n >= 769244604
              exact Brocard.berndt_galway_chunk_4278 n m (by omega) (by omega) h
          · -- n >= 769424460
            exact Brocard.berndt_galway_chunk_4279 n m (by omega) (by omega) h
        · -- n >= 769604316
          rcases Nat.lt_or_ge n 769964028 with hs4 | hs4
          · -- n < 769964028
            rcases Nat.lt_or_ge n 769784172 with hs5 | hs5
            · -- n < 769784172
              exact Brocard.berndt_galway_chunk_4280 n m (by omega) (by omega) h
            · -- n >= 769784172
              exact Brocard.berndt_galway_chunk_4281 n m (by omega) (by omega) h
          · -- n >= 769964028
            exact Brocard.berndt_galway_chunk_4282 n m (by omega) (by omega) h
      · -- n >= 770143884
        rcases Nat.lt_or_ge n 770683453 with hs3 | hs3
        · -- n < 770683453
          rcases Nat.lt_or_ge n 770503597 with hs4 | hs4
          · -- n < 770503597
            rcases Nat.lt_or_ge n 770323741 with hs5 | hs5
            · -- n < 770323741
              exact Brocard.berndt_galway_chunk_4283 n m (by omega) (by omega) h
            · -- n >= 770323741
              exact Brocard.berndt_galway_chunk_4284 n m (by omega) (by omega) h
          · -- n >= 770503597
            exact Brocard.berndt_galway_chunk_4285 n m (by omega) (by omega) h
        · -- n >= 770683453
          rcases Nat.lt_or_ge n 770863309 with hs4 | hs4
          · -- n < 770863309
            exact Brocard.berndt_galway_chunk_4286 n m (by omega) (by omega) h
          · -- n >= 770863309
            exact Brocard.berndt_galway_chunk_4287 n m (by omega) (by omega) h
  · -- n >= 771043165
    rcases Nat.lt_or_ge n 773201438 with hs1 | hs1
    · -- n < 773201438
      rcases Nat.lt_or_ge n 772122302 with hs2 | hs2
      · -- n < 772122302
        rcases Nat.lt_or_ge n 771582733 with hs3 | hs3
        · -- n < 771582733
          rcases Nat.lt_or_ge n 771402877 with hs4 | hs4
          · -- n < 771402877
            rcases Nat.lt_or_ge n 771223021 with hs5 | hs5
            · -- n < 771223021
              exact Brocard.berndt_galway_chunk_4288 n m (by omega) (by omega) h
            · -- n >= 771223021
              exact Brocard.berndt_galway_chunk_4289 n m (by omega) (by omega) h
          · -- n >= 771402877
            exact Brocard.berndt_galway_chunk_4290 n m (by omega) (by omega) h
        · -- n >= 771582733
          rcases Nat.lt_or_ge n 771942446 with hs4 | hs4
          · -- n < 771942446
            rcases Nat.lt_or_ge n 771762589 with hs5 | hs5
            · -- n < 771762589
              exact Brocard.berndt_galway_chunk_4291 n m (by omega) (by omega) h
            · -- n >= 771762589
              exact Brocard.berndt_galway_chunk_4292 n m (by omega) (by omega) h
          · -- n >= 771942446
            exact Brocard.berndt_galway_chunk_4293 n m (by omega) (by omega) h
      · -- n >= 772122302
        rcases Nat.lt_or_ge n 772661870 with hs3 | hs3
        · -- n < 772661870
          rcases Nat.lt_or_ge n 772482014 with hs4 | hs4
          · -- n < 772482014
            rcases Nat.lt_or_ge n 772302158 with hs5 | hs5
            · -- n < 772302158
              exact Brocard.berndt_galway_chunk_4294 n m (by omega) (by omega) h
            · -- n >= 772302158
              exact Brocard.berndt_galway_chunk_4295 n m (by omega) (by omega) h
          · -- n >= 772482014
            exact Brocard.berndt_galway_chunk_4296 n m (by omega) (by omega) h
        · -- n >= 772661870
          rcases Nat.lt_or_ge n 773021582 with hs4 | hs4
          · -- n < 773021582
            rcases Nat.lt_or_ge n 772841726 with hs5 | hs5
            · -- n < 772841726
              exact Brocard.berndt_galway_chunk_4297 n m (by omega) (by omega) h
            · -- n >= 772841726
              exact Brocard.berndt_galway_chunk_4298 n m (by omega) (by omega) h
          · -- n >= 773021582
            exact Brocard.berndt_galway_chunk_4299 n m (by omega) (by omega) h
    · -- n >= 773201438
      rcases Nat.lt_or_ge n 774280575 with hs2 | hs2
      · -- n < 774280575
        rcases Nat.lt_or_ge n 773741007 with hs3 | hs3
        · -- n < 773741007
          rcases Nat.lt_or_ge n 773561151 with hs4 | hs4
          · -- n < 773561151
            rcases Nat.lt_or_ge n 773381294 with hs5 | hs5
            · -- n < 773381294
              exact Brocard.berndt_galway_chunk_4300 n m (by omega) (by omega) h
            · -- n >= 773381294
              exact Brocard.berndt_galway_chunk_4301 n m (by omega) (by omega) h
          · -- n >= 773561151
            exact Brocard.berndt_galway_chunk_4302 n m (by omega) (by omega) h
        · -- n >= 773741007
          rcases Nat.lt_or_ge n 774100719 with hs4 | hs4
          · -- n < 774100719
            rcases Nat.lt_or_ge n 773920863 with hs5 | hs5
            · -- n < 773920863
              exact Brocard.berndt_galway_chunk_4303 n m (by omega) (by omega) h
            · -- n >= 773920863
              exact Brocard.berndt_galway_chunk_4304 n m (by omega) (by omega) h
          · -- n >= 774100719
            exact Brocard.berndt_galway_chunk_4305 n m (by omega) (by omega) h
      · -- n >= 774280575
        rcases Nat.lt_or_ge n 774820143 with hs3 | hs3
        · -- n < 774820143
          rcases Nat.lt_or_ge n 774640287 with hs4 | hs4
          · -- n < 774640287
            rcases Nat.lt_or_ge n 774460431 with hs5 | hs5
            · -- n < 774460431
              exact Brocard.berndt_galway_chunk_4306 n m (by omega) (by omega) h
            · -- n >= 774460431
              exact Brocard.berndt_galway_chunk_4307 n m (by omega) (by omega) h
          · -- n >= 774640287
            exact Brocard.berndt_galway_chunk_4308 n m (by omega) (by omega) h
        · -- n >= 774820143
          rcases Nat.lt_or_ge n 775000000 with hs4 | hs4
          · -- n < 775000000
            exact Brocard.berndt_galway_chunk_4309 n m (by omega) (by omega) h
          · -- n >= 775000000
            exact Brocard.berndt_galway_chunk_4310 n m (by omega) (by omega) h
