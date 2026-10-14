-- Prove2me | solution 1 for Brocard.berndt_galway_group_007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:22:04.670994+00:00
-- url     : https://prove2.me/submissions/0fc8ca72-6b60-42a3-8965-8c7b3756acc1

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0281
import Theorems.Thm_Brocard_berndt_galway_chunk_0282
import Theorems.Thm_Brocard_berndt_galway_chunk_0283
import Theorems.Thm_Brocard_berndt_galway_chunk_0284
import Theorems.Thm_Brocard_berndt_galway_chunk_0285
import Theorems.Thm_Brocard_berndt_galway_chunk_0286
import Theorems.Thm_Brocard_berndt_galway_chunk_0287
import Theorems.Thm_Brocard_berndt_galway_chunk_0288
import Theorems.Thm_Brocard_berndt_galway_chunk_0289
import Theorems.Thm_Brocard_berndt_galway_chunk_0290
import Theorems.Thm_Brocard_berndt_galway_chunk_0291
import Theorems.Thm_Brocard_berndt_galway_chunk_0292
import Theorems.Thm_Brocard_berndt_galway_chunk_0293
import Theorems.Thm_Brocard_berndt_galway_chunk_0294
import Theorems.Thm_Brocard_berndt_galway_chunk_0295
import Theorems.Thm_Brocard_berndt_galway_chunk_0296
import Theorems.Thm_Brocard_berndt_galway_chunk_0297
import Theorems.Thm_Brocard_berndt_galway_chunk_0298
import Theorems.Thm_Brocard_berndt_galway_chunk_0299
import Theorems.Thm_Brocard_berndt_galway_chunk_0300
import Theorems.Thm_Brocard_berndt_galway_chunk_0301
import Theorems.Thm_Brocard_berndt_galway_chunk_0302
import Theorems.Thm_Brocard_berndt_galway_chunk_0303
import Theorems.Thm_Brocard_berndt_galway_chunk_0304
import Theorems.Thm_Brocard_berndt_galway_chunk_0305
import Theorems.Thm_Brocard_berndt_galway_chunk_0306
import Theorems.Thm_Brocard_berndt_galway_chunk_0307
import Theorems.Thm_Brocard_berndt_galway_chunk_0308
import Theorems.Thm_Brocard_berndt_galway_chunk_0309
import Theorems.Thm_Brocard_berndt_galway_chunk_0310
import Theorems.Thm_Brocard_berndt_galway_chunk_0311
import Theorems.Thm_Brocard_berndt_galway_chunk_0312
import Theorems.Thm_Brocard_berndt_galway_chunk_0313
import Theorems.Thm_Brocard_berndt_galway_chunk_0314
import Theorems.Thm_Brocard_berndt_galway_chunk_0315
import Theorems.Thm_Brocard_berndt_galway_chunk_0316
import Theorems.Thm_Brocard_berndt_galway_chunk_0317
import Theorems.Thm_Brocard_berndt_galway_chunk_0318
import Theorems.Thm_Brocard_berndt_galway_chunk_0319
import Theorems.Thm_Brocard_berndt_galway_chunk_0320
import Theorems.Thm_Brocard_berndt_galway_chunk_0321
import Theorems.Thm_Brocard_berndt_galway_chunk_0322
import Theorems.Thm_Brocard_berndt_galway_chunk_0323
import Theorems.Thm_Brocard_berndt_galway_chunk_0324
import Theorems.Thm_Brocard_berndt_galway_chunk_0325
import Theorems.Thm_Brocard_berndt_galway_chunk_0326

theorem solution (n m : ℕ) (h1 : 50359716 ≤ n) (h2 : n < 58633096) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 54496406 with hs0 | hs0
  · -- n < 54496406
    rcases Nat.lt_or_ge n 52517989 with hs1 | hs1
    · -- n < 52517989
      rcases Nat.lt_or_ge n 51438852 with hs2 | hs2
      · -- n < 51438852
        rcases Nat.lt_or_ge n 50899284 with hs3 | hs3
        · -- n < 50899284
          rcases Nat.lt_or_ge n 50719428 with hs4 | hs4
          · -- n < 50719428
            rcases Nat.lt_or_ge n 50539572 with hs5 | hs5
            · -- n < 50539572
              exact Brocard.berndt_galway_chunk_0281 n m (by omega) (by omega) h
            · -- n >= 50539572
              exact Brocard.berndt_galway_chunk_0282 n m (by omega) (by omega) h
          · -- n >= 50719428
            exact Brocard.berndt_galway_chunk_0283 n m (by omega) (by omega) h
        · -- n >= 50899284
          rcases Nat.lt_or_ge n 51258996 with hs4 | hs4
          · -- n < 51258996
            rcases Nat.lt_or_ge n 51079140 with hs5 | hs5
            · -- n < 51079140
              exact Brocard.berndt_galway_chunk_0284 n m (by omega) (by omega) h
            · -- n >= 51079140
              exact Brocard.berndt_galway_chunk_0285 n m (by omega) (by omega) h
          · -- n >= 51258996
            exact Brocard.berndt_galway_chunk_0286 n m (by omega) (by omega) h
      · -- n >= 51438852
        rcases Nat.lt_or_ge n 51978421 with hs3 | hs3
        · -- n < 51978421
          rcases Nat.lt_or_ge n 51798565 with hs4 | hs4
          · -- n < 51798565
            rcases Nat.lt_or_ge n 51618708 with hs5 | hs5
            · -- n < 51618708
              exact Brocard.berndt_galway_chunk_0287 n m (by omega) (by omega) h
            · -- n >= 51618708
              exact Brocard.berndt_galway_chunk_0288 n m (by omega) (by omega) h
          · -- n >= 51798565
            exact Brocard.berndt_galway_chunk_0289 n m (by omega) (by omega) h
        · -- n >= 51978421
          rcases Nat.lt_or_ge n 52338133 with hs4 | hs4
          · -- n < 52338133
            rcases Nat.lt_or_ge n 52158277 with hs5 | hs5
            · -- n < 52158277
              exact Brocard.berndt_galway_chunk_0290 n m (by omega) (by omega) h
            · -- n >= 52158277
              exact Brocard.berndt_galway_chunk_0291 n m (by omega) (by omega) h
          · -- n >= 52338133
            exact Brocard.berndt_galway_chunk_0292 n m (by omega) (by omega) h
    · -- n >= 52517989
      rcases Nat.lt_or_ge n 53597126 with hs2 | hs2
      · -- n < 53597126
        rcases Nat.lt_or_ge n 53057557 with hs3 | hs3
        · -- n < 53057557
          rcases Nat.lt_or_ge n 52877701 with hs4 | hs4
          · -- n < 52877701
            rcases Nat.lt_or_ge n 52697845 with hs5 | hs5
            · -- n < 52697845
              exact Brocard.berndt_galway_chunk_0293 n m (by omega) (by omega) h
            · -- n >= 52697845
              exact Brocard.berndt_galway_chunk_0294 n m (by omega) (by omega) h
          · -- n >= 52877701
            exact Brocard.berndt_galway_chunk_0295 n m (by omega) (by omega) h
        · -- n >= 53057557
          rcases Nat.lt_or_ge n 53417269 with hs4 | hs4
          · -- n < 53417269
            rcases Nat.lt_or_ge n 53237413 with hs5 | hs5
            · -- n < 53237413
              exact Brocard.berndt_galway_chunk_0296 n m (by omega) (by omega) h
            · -- n >= 53237413
              exact Brocard.berndt_galway_chunk_0297 n m (by omega) (by omega) h
          · -- n >= 53417269
            exact Brocard.berndt_galway_chunk_0298 n m (by omega) (by omega) h
      · -- n >= 53597126
        rcases Nat.lt_or_ge n 54136694 with hs3 | hs3
        · -- n < 54136694
          rcases Nat.lt_or_ge n 53956838 with hs4 | hs4
          · -- n < 53956838
            rcases Nat.lt_or_ge n 53776982 with hs5 | hs5
            · -- n < 53776982
              exact Brocard.berndt_galway_chunk_0299 n m (by omega) (by omega) h
            · -- n >= 53776982
              exact Brocard.berndt_galway_chunk_0300 n m (by omega) (by omega) h
          · -- n >= 53956838
            exact Brocard.berndt_galway_chunk_0301 n m (by omega) (by omega) h
        · -- n >= 54136694
          rcases Nat.lt_or_ge n 54316550 with hs4 | hs4
          · -- n < 54316550
            exact Brocard.berndt_galway_chunk_0302 n m (by omega) (by omega) h
          · -- n >= 54316550
            exact Brocard.berndt_galway_chunk_0303 n m (by omega) (by omega) h
  · -- n >= 54496406
    rcases Nat.lt_or_ge n 56654679 with hs1 | hs1
    · -- n < 56654679
      rcases Nat.lt_or_ge n 55575543 with hs2 | hs2
      · -- n < 55575543
        rcases Nat.lt_or_ge n 55035974 with hs3 | hs3
        · -- n < 55035974
          rcases Nat.lt_or_ge n 54856118 with hs4 | hs4
          · -- n < 54856118
            rcases Nat.lt_or_ge n 54676262 with hs5 | hs5
            · -- n < 54676262
              exact Brocard.berndt_galway_chunk_0304 n m (by omega) (by omega) h
            · -- n >= 54676262
              exact Brocard.berndt_galway_chunk_0305 n m (by omega) (by omega) h
          · -- n >= 54856118
            exact Brocard.berndt_galway_chunk_0306 n m (by omega) (by omega) h
        · -- n >= 55035974
          rcases Nat.lt_or_ge n 55395687 with hs4 | hs4
          · -- n < 55395687
            rcases Nat.lt_or_ge n 55215830 with hs5 | hs5
            · -- n < 55215830
              exact Brocard.berndt_galway_chunk_0307 n m (by omega) (by omega) h
            · -- n >= 55215830
              exact Brocard.berndt_galway_chunk_0308 n m (by omega) (by omega) h
          · -- n >= 55395687
            exact Brocard.berndt_galway_chunk_0309 n m (by omega) (by omega) h
      · -- n >= 55575543
        rcases Nat.lt_or_ge n 56115111 with hs3 | hs3
        · -- n < 56115111
          rcases Nat.lt_or_ge n 55935255 with hs4 | hs4
          · -- n < 55935255
            rcases Nat.lt_or_ge n 55755399 with hs5 | hs5
            · -- n < 55755399
              exact Brocard.berndt_galway_chunk_0310 n m (by omega) (by omega) h
            · -- n >= 55755399
              exact Brocard.berndt_galway_chunk_0311 n m (by omega) (by omega) h
          · -- n >= 55935255
            exact Brocard.berndt_galway_chunk_0312 n m (by omega) (by omega) h
        · -- n >= 56115111
          rcases Nat.lt_or_ge n 56474823 with hs4 | hs4
          · -- n < 56474823
            rcases Nat.lt_or_ge n 56294967 with hs5 | hs5
            · -- n < 56294967
              exact Brocard.berndt_galway_chunk_0313 n m (by omega) (by omega) h
            · -- n >= 56294967
              exact Brocard.berndt_galway_chunk_0314 n m (by omega) (by omega) h
          · -- n >= 56474823
            exact Brocard.berndt_galway_chunk_0315 n m (by omega) (by omega) h
    · -- n >= 56654679
      rcases Nat.lt_or_ge n 57733816 with hs2 | hs2
      · -- n < 57733816
        rcases Nat.lt_or_ge n 57194248 with hs3 | hs3
        · -- n < 57194248
          rcases Nat.lt_or_ge n 57014391 with hs4 | hs4
          · -- n < 57014391
            rcases Nat.lt_or_ge n 56834535 with hs5 | hs5
            · -- n < 56834535
              exact Brocard.berndt_galway_chunk_0316 n m (by omega) (by omega) h
            · -- n >= 56834535
              exact Brocard.berndt_galway_chunk_0317 n m (by omega) (by omega) h
          · -- n >= 57014391
            exact Brocard.berndt_galway_chunk_0318 n m (by omega) (by omega) h
        · -- n >= 57194248
          rcases Nat.lt_or_ge n 57553960 with hs4 | hs4
          · -- n < 57553960
            rcases Nat.lt_or_ge n 57374104 with hs5 | hs5
            · -- n < 57374104
              exact Brocard.berndt_galway_chunk_0319 n m (by omega) (by omega) h
            · -- n >= 57374104
              exact Brocard.berndt_galway_chunk_0320 n m (by omega) (by omega) h
          · -- n >= 57553960
            exact Brocard.berndt_galway_chunk_0321 n m (by omega) (by omega) h
      · -- n >= 57733816
        rcases Nat.lt_or_ge n 58273384 with hs3 | hs3
        · -- n < 58273384
          rcases Nat.lt_or_ge n 58093528 with hs4 | hs4
          · -- n < 58093528
            rcases Nat.lt_or_ge n 57913672 with hs5 | hs5
            · -- n < 57913672
              exact Brocard.berndt_galway_chunk_0322 n m (by omega) (by omega) h
            · -- n >= 57913672
              exact Brocard.berndt_galway_chunk_0323 n m (by omega) (by omega) h
          · -- n >= 58093528
            exact Brocard.berndt_galway_chunk_0324 n m (by omega) (by omega) h
        · -- n >= 58273384
          rcases Nat.lt_or_ge n 58453240 with hs4 | hs4
          · -- n < 58453240
            exact Brocard.berndt_galway_chunk_0325 n m (by omega) (by omega) h
          · -- n >= 58453240
            exact Brocard.berndt_galway_chunk_0326 n m (by omega) (by omega) h
