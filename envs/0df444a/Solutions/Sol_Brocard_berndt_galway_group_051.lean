-- Prove2me | solution 1 for Brocard.berndt_galway_group_051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:35:39.418246+00:00
-- url     : https://prove2.me/submissions/910b49e4-39bb-4ae0-ad32-31281c9c31d9

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_2319
import Theorems.Thm_Brocard_berndt_galway_chunk_2320
import Theorems.Thm_Brocard_berndt_galway_chunk_2321
import Theorems.Thm_Brocard_berndt_galway_chunk_2322
import Theorems.Thm_Brocard_berndt_galway_chunk_2323
import Theorems.Thm_Brocard_berndt_galway_chunk_2324
import Theorems.Thm_Brocard_berndt_galway_chunk_2325
import Theorems.Thm_Brocard_berndt_galway_chunk_2326
import Theorems.Thm_Brocard_berndt_galway_chunk_2327
import Theorems.Thm_Brocard_berndt_galway_chunk_2328
import Theorems.Thm_Brocard_berndt_galway_chunk_2329
import Theorems.Thm_Brocard_berndt_galway_chunk_2330
import Theorems.Thm_Brocard_berndt_galway_chunk_2331
import Theorems.Thm_Brocard_berndt_galway_chunk_2332
import Theorems.Thm_Brocard_berndt_galway_chunk_2333
import Theorems.Thm_Brocard_berndt_galway_chunk_2334
import Theorems.Thm_Brocard_berndt_galway_chunk_2335
import Theorems.Thm_Brocard_berndt_galway_chunk_2336
import Theorems.Thm_Brocard_berndt_galway_chunk_2337
import Theorems.Thm_Brocard_berndt_galway_chunk_2338
import Theorems.Thm_Brocard_berndt_galway_chunk_2339
import Theorems.Thm_Brocard_berndt_galway_chunk_2340
import Theorems.Thm_Brocard_berndt_galway_chunk_2341
import Theorems.Thm_Brocard_berndt_galway_chunk_2342
import Theorems.Thm_Brocard_berndt_galway_chunk_2343
import Theorems.Thm_Brocard_berndt_galway_chunk_2344
import Theorems.Thm_Brocard_berndt_galway_chunk_2345
import Theorems.Thm_Brocard_berndt_galway_chunk_2346
import Theorems.Thm_Brocard_berndt_galway_chunk_2347
import Theorems.Thm_Brocard_berndt_galway_chunk_2348
import Theorems.Thm_Brocard_berndt_galway_chunk_2349
import Theorems.Thm_Brocard_berndt_galway_chunk_2350
import Theorems.Thm_Brocard_berndt_galway_chunk_2351
import Theorems.Thm_Brocard_berndt_galway_chunk_2352
import Theorems.Thm_Brocard_berndt_galway_chunk_2353
import Theorems.Thm_Brocard_berndt_galway_chunk_2354
import Theorems.Thm_Brocard_berndt_galway_chunk_2355
import Theorems.Thm_Brocard_berndt_galway_chunk_2356
import Theorems.Thm_Brocard_berndt_galway_chunk_2357
import Theorems.Thm_Brocard_berndt_galway_chunk_2358
import Theorems.Thm_Brocard_berndt_galway_chunk_2359
import Theorems.Thm_Brocard_berndt_galway_chunk_2360
import Theorems.Thm_Brocard_berndt_galway_chunk_2361
import Theorems.Thm_Brocard_berndt_galway_chunk_2362
import Theorems.Thm_Brocard_berndt_galway_chunk_2363
import Theorems.Thm_Brocard_berndt_galway_chunk_2364
import Theorems.Thm_Brocard_berndt_galway_chunk_2365

theorem solution (n m : ℕ) (h1 : 416906474 ≤ n) (h2 : n < 425359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 421223021 with hs0 | hs0
  · -- n < 421223021
    rcases Nat.lt_or_ge n 419064748 with hs1 | hs1
    · -- n < 419064748
      rcases Nat.lt_or_ge n 417985611 with hs2 | hs2
      · -- n < 417985611
        rcases Nat.lt_or_ge n 417446043 with hs3 | hs3
        · -- n < 417446043
          rcases Nat.lt_or_ge n 417266187 with hs4 | hs4
          · -- n < 417266187
            rcases Nat.lt_or_ge n 417086330 with hs5 | hs5
            · -- n < 417086330
              exact Brocard.berndt_galway_chunk_2319 n m (by omega) (by omega) h
            · -- n >= 417086330
              exact Brocard.berndt_galway_chunk_2320 n m (by omega) (by omega) h
          · -- n >= 417266187
            exact Brocard.berndt_galway_chunk_2321 n m (by omega) (by omega) h
        · -- n >= 417446043
          rcases Nat.lt_or_ge n 417805755 with hs4 | hs4
          · -- n < 417805755
            rcases Nat.lt_or_ge n 417625899 with hs5 | hs5
            · -- n < 417625899
              exact Brocard.berndt_galway_chunk_2322 n m (by omega) (by omega) h
            · -- n >= 417625899
              exact Brocard.berndt_galway_chunk_2323 n m (by omega) (by omega) h
          · -- n >= 417805755
            exact Brocard.berndt_galway_chunk_2324 n m (by omega) (by omega) h
      · -- n >= 417985611
        rcases Nat.lt_or_ge n 418525179 with hs3 | hs3
        · -- n < 418525179
          rcases Nat.lt_or_ge n 418345323 with hs4 | hs4
          · -- n < 418345323
            rcases Nat.lt_or_ge n 418165467 with hs5 | hs5
            · -- n < 418165467
              exact Brocard.berndt_galway_chunk_2325 n m (by omega) (by omega) h
            · -- n >= 418165467
              exact Brocard.berndt_galway_chunk_2326 n m (by omega) (by omega) h
          · -- n >= 418345323
            exact Brocard.berndt_galway_chunk_2327 n m (by omega) (by omega) h
        · -- n >= 418525179
          rcases Nat.lt_or_ge n 418884892 with hs4 | hs4
          · -- n < 418884892
            rcases Nat.lt_or_ge n 418705035 with hs5 | hs5
            · -- n < 418705035
              exact Brocard.berndt_galway_chunk_2328 n m (by omega) (by omega) h
            · -- n >= 418705035
              exact Brocard.berndt_galway_chunk_2329 n m (by omega) (by omega) h
          · -- n >= 418884892
            exact Brocard.berndt_galway_chunk_2330 n m (by omega) (by omega) h
    · -- n >= 419064748
      rcases Nat.lt_or_ge n 420143884 with hs2 | hs2
      · -- n < 420143884
        rcases Nat.lt_or_ge n 419604316 with hs3 | hs3
        · -- n < 419604316
          rcases Nat.lt_or_ge n 419424460 with hs4 | hs4
          · -- n < 419424460
            rcases Nat.lt_or_ge n 419244604 with hs5 | hs5
            · -- n < 419244604
              exact Brocard.berndt_galway_chunk_2331 n m (by omega) (by omega) h
            · -- n >= 419244604
              exact Brocard.berndt_galway_chunk_2332 n m (by omega) (by omega) h
          · -- n >= 419424460
            exact Brocard.berndt_galway_chunk_2333 n m (by omega) (by omega) h
        · -- n >= 419604316
          rcases Nat.lt_or_ge n 419964028 with hs4 | hs4
          · -- n < 419964028
            rcases Nat.lt_or_ge n 419784172 with hs5 | hs5
            · -- n < 419784172
              exact Brocard.berndt_galway_chunk_2334 n m (by omega) (by omega) h
            · -- n >= 419784172
              exact Brocard.berndt_galway_chunk_2335 n m (by omega) (by omega) h
          · -- n >= 419964028
            exact Brocard.berndt_galway_chunk_2336 n m (by omega) (by omega) h
      · -- n >= 420143884
        rcases Nat.lt_or_ge n 420683453 with hs3 | hs3
        · -- n < 420683453
          rcases Nat.lt_or_ge n 420503597 with hs4 | hs4
          · -- n < 420503597
            rcases Nat.lt_or_ge n 420323741 with hs5 | hs5
            · -- n < 420323741
              exact Brocard.berndt_galway_chunk_2337 n m (by omega) (by omega) h
            · -- n >= 420323741
              exact Brocard.berndt_galway_chunk_2338 n m (by omega) (by omega) h
          · -- n >= 420503597
            exact Brocard.berndt_galway_chunk_2339 n m (by omega) (by omega) h
        · -- n >= 420683453
          rcases Nat.lt_or_ge n 421043165 with hs4 | hs4
          · -- n < 421043165
            rcases Nat.lt_or_ge n 420863309 with hs5 | hs5
            · -- n < 420863309
              exact Brocard.berndt_galway_chunk_2340 n m (by omega) (by omega) h
            · -- n >= 420863309
              exact Brocard.berndt_galway_chunk_2341 n m (by omega) (by omega) h
          · -- n >= 421043165
            exact Brocard.berndt_galway_chunk_2342 n m (by omega) (by omega) h
  · -- n >= 421223021
    rcases Nat.lt_or_ge n 423381294 with hs1 | hs1
    · -- n < 423381294
      rcases Nat.lt_or_ge n 422302158 with hs2 | hs2
      · -- n < 422302158
        rcases Nat.lt_or_ge n 421762589 with hs3 | hs3
        · -- n < 421762589
          rcases Nat.lt_or_ge n 421582733 with hs4 | hs4
          · -- n < 421582733
            rcases Nat.lt_or_ge n 421402877 with hs5 | hs5
            · -- n < 421402877
              exact Brocard.berndt_galway_chunk_2343 n m (by omega) (by omega) h
            · -- n >= 421402877
              exact Brocard.berndt_galway_chunk_2344 n m (by omega) (by omega) h
          · -- n >= 421582733
            exact Brocard.berndt_galway_chunk_2345 n m (by omega) (by omega) h
        · -- n >= 421762589
          rcases Nat.lt_or_ge n 422122302 with hs4 | hs4
          · -- n < 422122302
            rcases Nat.lt_or_ge n 421942446 with hs5 | hs5
            · -- n < 421942446
              exact Brocard.berndt_galway_chunk_2346 n m (by omega) (by omega) h
            · -- n >= 421942446
              exact Brocard.berndt_galway_chunk_2347 n m (by omega) (by omega) h
          · -- n >= 422122302
            exact Brocard.berndt_galway_chunk_2348 n m (by omega) (by omega) h
      · -- n >= 422302158
        rcases Nat.lt_or_ge n 422841726 with hs3 | hs3
        · -- n < 422841726
          rcases Nat.lt_or_ge n 422661870 with hs4 | hs4
          · -- n < 422661870
            rcases Nat.lt_or_ge n 422482014 with hs5 | hs5
            · -- n < 422482014
              exact Brocard.berndt_galway_chunk_2349 n m (by omega) (by omega) h
            · -- n >= 422482014
              exact Brocard.berndt_galway_chunk_2350 n m (by omega) (by omega) h
          · -- n >= 422661870
            exact Brocard.berndt_galway_chunk_2351 n m (by omega) (by omega) h
        · -- n >= 422841726
          rcases Nat.lt_or_ge n 423201438 with hs4 | hs4
          · -- n < 423201438
            rcases Nat.lt_or_ge n 423021582 with hs5 | hs5
            · -- n < 423021582
              exact Brocard.berndt_galway_chunk_2352 n m (by omega) (by omega) h
            · -- n >= 423021582
              exact Brocard.berndt_galway_chunk_2353 n m (by omega) (by omega) h
          · -- n >= 423201438
            exact Brocard.berndt_galway_chunk_2354 n m (by omega) (by omega) h
    · -- n >= 423381294
      rcases Nat.lt_or_ge n 424460431 with hs2 | hs2
      · -- n < 424460431
        rcases Nat.lt_or_ge n 423920863 with hs3 | hs3
        · -- n < 423920863
          rcases Nat.lt_or_ge n 423741007 with hs4 | hs4
          · -- n < 423741007
            rcases Nat.lt_or_ge n 423561151 with hs5 | hs5
            · -- n < 423561151
              exact Brocard.berndt_galway_chunk_2355 n m (by omega) (by omega) h
            · -- n >= 423561151
              exact Brocard.berndt_galway_chunk_2356 n m (by omega) (by omega) h
          · -- n >= 423741007
            exact Brocard.berndt_galway_chunk_2357 n m (by omega) (by omega) h
        · -- n >= 423920863
          rcases Nat.lt_or_ge n 424280575 with hs4 | hs4
          · -- n < 424280575
            rcases Nat.lt_or_ge n 424100719 with hs5 | hs5
            · -- n < 424100719
              exact Brocard.berndt_galway_chunk_2358 n m (by omega) (by omega) h
            · -- n >= 424100719
              exact Brocard.berndt_galway_chunk_2359 n m (by omega) (by omega) h
          · -- n >= 424280575
            exact Brocard.berndt_galway_chunk_2360 n m (by omega) (by omega) h
      · -- n >= 424460431
        rcases Nat.lt_or_ge n 425000000 with hs3 | hs3
        · -- n < 425000000
          rcases Nat.lt_or_ge n 424820143 with hs4 | hs4
          · -- n < 424820143
            rcases Nat.lt_or_ge n 424640287 with hs5 | hs5
            · -- n < 424640287
              exact Brocard.berndt_galway_chunk_2361 n m (by omega) (by omega) h
            · -- n >= 424640287
              exact Brocard.berndt_galway_chunk_2362 n m (by omega) (by omega) h
          · -- n >= 424820143
            exact Brocard.berndt_galway_chunk_2363 n m (by omega) (by omega) h
        · -- n >= 425000000
          rcases Nat.lt_or_ge n 425179856 with hs4 | hs4
          · -- n < 425179856
            exact Brocard.berndt_galway_chunk_2364 n m (by omega) (by omega) h
          · -- n >= 425179856
            exact Brocard.berndt_galway_chunk_2365 n m (by omega) (by omega) h
