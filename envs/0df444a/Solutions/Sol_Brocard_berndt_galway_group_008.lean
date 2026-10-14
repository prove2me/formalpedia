-- Prove2me | solution 1 for Brocard.berndt_galway_group_008
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:36:58.758597+00:00
-- url     : https://prove2.me/submissions/9be92152-f33e-47e2-89d5-ffe8d1bfcb89

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0327
import Theorems.Thm_Brocard_berndt_galway_chunk_0328
import Theorems.Thm_Brocard_berndt_galway_chunk_0329
import Theorems.Thm_Brocard_berndt_galway_chunk_0330
import Theorems.Thm_Brocard_berndt_galway_chunk_0331
import Theorems.Thm_Brocard_berndt_galway_chunk_0332
import Theorems.Thm_Brocard_berndt_galway_chunk_0333
import Theorems.Thm_Brocard_berndt_galway_chunk_0334
import Theorems.Thm_Brocard_berndt_galway_chunk_0335
import Theorems.Thm_Brocard_berndt_galway_chunk_0336
import Theorems.Thm_Brocard_berndt_galway_chunk_0337
import Theorems.Thm_Brocard_berndt_galway_chunk_0338
import Theorems.Thm_Brocard_berndt_galway_chunk_0339
import Theorems.Thm_Brocard_berndt_galway_chunk_0340
import Theorems.Thm_Brocard_berndt_galway_chunk_0341
import Theorems.Thm_Brocard_berndt_galway_chunk_0342
import Theorems.Thm_Brocard_berndt_galway_chunk_0343
import Theorems.Thm_Brocard_berndt_galway_chunk_0344
import Theorems.Thm_Brocard_berndt_galway_chunk_0345
import Theorems.Thm_Brocard_berndt_galway_chunk_0346
import Theorems.Thm_Brocard_berndt_galway_chunk_0347
import Theorems.Thm_Brocard_berndt_galway_chunk_0348
import Theorems.Thm_Brocard_berndt_galway_chunk_0349
import Theorems.Thm_Brocard_berndt_galway_chunk_0350
import Theorems.Thm_Brocard_berndt_galway_chunk_0351
import Theorems.Thm_Brocard_berndt_galway_chunk_0352
import Theorems.Thm_Brocard_berndt_galway_chunk_0353
import Theorems.Thm_Brocard_berndt_galway_chunk_0354
import Theorems.Thm_Brocard_berndt_galway_chunk_0355
import Theorems.Thm_Brocard_berndt_galway_chunk_0356
import Theorems.Thm_Brocard_berndt_galway_chunk_0357
import Theorems.Thm_Brocard_berndt_galway_chunk_0358
import Theorems.Thm_Brocard_berndt_galway_chunk_0359
import Theorems.Thm_Brocard_berndt_galway_chunk_0360
import Theorems.Thm_Brocard_berndt_galway_chunk_0361
import Theorems.Thm_Brocard_berndt_galway_chunk_0362
import Theorems.Thm_Brocard_berndt_galway_chunk_0363
import Theorems.Thm_Brocard_berndt_galway_chunk_0364
import Theorems.Thm_Brocard_berndt_galway_chunk_0365
import Theorems.Thm_Brocard_berndt_galway_chunk_0366
import Theorems.Thm_Brocard_berndt_galway_chunk_0367
import Theorems.Thm_Brocard_berndt_galway_chunk_0368
import Theorems.Thm_Brocard_berndt_galway_chunk_0369
import Theorems.Thm_Brocard_berndt_galway_chunk_0370
import Theorems.Thm_Brocard_berndt_galway_chunk_0371
import Theorems.Thm_Brocard_berndt_galway_chunk_0372

theorem solution (n m : ℕ) (h1 : 58633096 ≤ n) (h2 : n < 66906477) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 62769787 with hs0 | hs0
  · -- n < 62769787
    rcases Nat.lt_or_ge n 60791370 with hs1 | hs1
    · -- n < 60791370
      rcases Nat.lt_or_ge n 59712233 with hs2 | hs2
      · -- n < 59712233
        rcases Nat.lt_or_ge n 59172665 with hs3 | hs3
        · -- n < 59172665
          rcases Nat.lt_or_ge n 58992809 with hs4 | hs4
          · -- n < 58992809
            rcases Nat.lt_or_ge n 58812952 with hs5 | hs5
            · -- n < 58812952
              exact Brocard.berndt_galway_chunk_0327 n m (by omega) (by omega) h
            · -- n >= 58812952
              exact Brocard.berndt_galway_chunk_0328 n m (by omega) (by omega) h
          · -- n >= 58992809
            exact Brocard.berndt_galway_chunk_0329 n m (by omega) (by omega) h
        · -- n >= 59172665
          rcases Nat.lt_or_ge n 59532377 with hs4 | hs4
          · -- n < 59532377
            rcases Nat.lt_or_ge n 59352521 with hs5 | hs5
            · -- n < 59352521
              exact Brocard.berndt_galway_chunk_0330 n m (by omega) (by omega) h
            · -- n >= 59352521
              exact Brocard.berndt_galway_chunk_0331 n m (by omega) (by omega) h
          · -- n >= 59532377
            exact Brocard.berndt_galway_chunk_0332 n m (by omega) (by omega) h
      · -- n >= 59712233
        rcases Nat.lt_or_ge n 60251801 with hs3 | hs3
        · -- n < 60251801
          rcases Nat.lt_or_ge n 60071945 with hs4 | hs4
          · -- n < 60071945
            rcases Nat.lt_or_ge n 59892089 with hs5 | hs5
            · -- n < 59892089
              exact Brocard.berndt_galway_chunk_0333 n m (by omega) (by omega) h
            · -- n >= 59892089
              exact Brocard.berndt_galway_chunk_0334 n m (by omega) (by omega) h
          · -- n >= 60071945
            exact Brocard.berndt_galway_chunk_0335 n m (by omega) (by omega) h
        · -- n >= 60251801
          rcases Nat.lt_or_ge n 60611513 with hs4 | hs4
          · -- n < 60611513
            rcases Nat.lt_or_ge n 60431657 with hs5 | hs5
            · -- n < 60431657
              exact Brocard.berndt_galway_chunk_0336 n m (by omega) (by omega) h
            · -- n >= 60431657
              exact Brocard.berndt_galway_chunk_0337 n m (by omega) (by omega) h
          · -- n >= 60611513
            exact Brocard.berndt_galway_chunk_0338 n m (by omega) (by omega) h
    · -- n >= 60791370
      rcases Nat.lt_or_ge n 61870506 with hs2 | hs2
      · -- n < 61870506
        rcases Nat.lt_or_ge n 61330938 with hs3 | hs3
        · -- n < 61330938
          rcases Nat.lt_or_ge n 61151082 with hs4 | hs4
          · -- n < 61151082
            rcases Nat.lt_or_ge n 60971226 with hs5 | hs5
            · -- n < 60971226
              exact Brocard.berndt_galway_chunk_0339 n m (by omega) (by omega) h
            · -- n >= 60971226
              exact Brocard.berndt_galway_chunk_0340 n m (by omega) (by omega) h
          · -- n >= 61151082
            exact Brocard.berndt_galway_chunk_0341 n m (by omega) (by omega) h
        · -- n >= 61330938
          rcases Nat.lt_or_ge n 61690650 with hs4 | hs4
          · -- n < 61690650
            rcases Nat.lt_or_ge n 61510794 with hs5 | hs5
            · -- n < 61510794
              exact Brocard.berndt_galway_chunk_0342 n m (by omega) (by omega) h
            · -- n >= 61510794
              exact Brocard.berndt_galway_chunk_0343 n m (by omega) (by omega) h
          · -- n >= 61690650
            exact Brocard.berndt_galway_chunk_0344 n m (by omega) (by omega) h
      · -- n >= 61870506
        rcases Nat.lt_or_ge n 62410074 with hs3 | hs3
        · -- n < 62410074
          rcases Nat.lt_or_ge n 62230218 with hs4 | hs4
          · -- n < 62230218
            rcases Nat.lt_or_ge n 62050362 with hs5 | hs5
            · -- n < 62050362
              exact Brocard.berndt_galway_chunk_0345 n m (by omega) (by omega) h
            · -- n >= 62050362
              exact Brocard.berndt_galway_chunk_0346 n m (by omega) (by omega) h
          · -- n >= 62230218
            exact Brocard.berndt_galway_chunk_0347 n m (by omega) (by omega) h
        · -- n >= 62410074
          rcases Nat.lt_or_ge n 62589931 with hs4 | hs4
          · -- n < 62589931
            exact Brocard.berndt_galway_chunk_0348 n m (by omega) (by omega) h
          · -- n >= 62589931
            exact Brocard.berndt_galway_chunk_0349 n m (by omega) (by omega) h
  · -- n >= 62769787
    rcases Nat.lt_or_ge n 64928060 with hs1 | hs1
    · -- n < 64928060
      rcases Nat.lt_or_ge n 63848923 with hs2 | hs2
      · -- n < 63848923
        rcases Nat.lt_or_ge n 63309355 with hs3 | hs3
        · -- n < 63309355
          rcases Nat.lt_or_ge n 63129499 with hs4 | hs4
          · -- n < 63129499
            rcases Nat.lt_or_ge n 62949643 with hs5 | hs5
            · -- n < 62949643
              exact Brocard.berndt_galway_chunk_0350 n m (by omega) (by omega) h
            · -- n >= 62949643
              exact Brocard.berndt_galway_chunk_0351 n m (by omega) (by omega) h
          · -- n >= 63129499
            exact Brocard.berndt_galway_chunk_0352 n m (by omega) (by omega) h
        · -- n >= 63309355
          rcases Nat.lt_or_ge n 63669067 with hs4 | hs4
          · -- n < 63669067
            rcases Nat.lt_or_ge n 63489211 with hs5 | hs5
            · -- n < 63489211
              exact Brocard.berndt_galway_chunk_0353 n m (by omega) (by omega) h
            · -- n >= 63489211
              exact Brocard.berndt_galway_chunk_0354 n m (by omega) (by omega) h
          · -- n >= 63669067
            exact Brocard.berndt_galway_chunk_0355 n m (by omega) (by omega) h
      · -- n >= 63848923
        rcases Nat.lt_or_ge n 64388492 with hs3 | hs3
        · -- n < 64388492
          rcases Nat.lt_or_ge n 64208635 with hs4 | hs4
          · -- n < 64208635
            rcases Nat.lt_or_ge n 64028779 with hs5 | hs5
            · -- n < 64028779
              exact Brocard.berndt_galway_chunk_0356 n m (by omega) (by omega) h
            · -- n >= 64028779
              exact Brocard.berndt_galway_chunk_0357 n m (by omega) (by omega) h
          · -- n >= 64208635
            exact Brocard.berndt_galway_chunk_0358 n m (by omega) (by omega) h
        · -- n >= 64388492
          rcases Nat.lt_or_ge n 64748204 with hs4 | hs4
          · -- n < 64748204
            rcases Nat.lt_or_ge n 64568348 with hs5 | hs5
            · -- n < 64568348
              exact Brocard.berndt_galway_chunk_0359 n m (by omega) (by omega) h
            · -- n >= 64568348
              exact Brocard.berndt_galway_chunk_0360 n m (by omega) (by omega) h
          · -- n >= 64748204
            exact Brocard.berndt_galway_chunk_0361 n m (by omega) (by omega) h
    · -- n >= 64928060
      rcases Nat.lt_or_ge n 66007196 with hs2 | hs2
      · -- n < 66007196
        rcases Nat.lt_or_ge n 65467628 with hs3 | hs3
        · -- n < 65467628
          rcases Nat.lt_or_ge n 65287772 with hs4 | hs4
          · -- n < 65287772
            rcases Nat.lt_or_ge n 65107916 with hs5 | hs5
            · -- n < 65107916
              exact Brocard.berndt_galway_chunk_0362 n m (by omega) (by omega) h
            · -- n >= 65107916
              exact Brocard.berndt_galway_chunk_0363 n m (by omega) (by omega) h
          · -- n >= 65287772
            exact Brocard.berndt_galway_chunk_0364 n m (by omega) (by omega) h
        · -- n >= 65467628
          rcases Nat.lt_or_ge n 65827340 with hs4 | hs4
          · -- n < 65827340
            rcases Nat.lt_or_ge n 65647484 with hs5 | hs5
            · -- n < 65647484
              exact Brocard.berndt_galway_chunk_0365 n m (by omega) (by omega) h
            · -- n >= 65647484
              exact Brocard.berndt_galway_chunk_0366 n m (by omega) (by omega) h
          · -- n >= 65827340
            exact Brocard.berndt_galway_chunk_0367 n m (by omega) (by omega) h
      · -- n >= 66007196
        rcases Nat.lt_or_ge n 66546765 with hs3 | hs3
        · -- n < 66546765
          rcases Nat.lt_or_ge n 66366909 with hs4 | hs4
          · -- n < 66366909
            rcases Nat.lt_or_ge n 66187053 with hs5 | hs5
            · -- n < 66187053
              exact Brocard.berndt_galway_chunk_0368 n m (by omega) (by omega) h
            · -- n >= 66187053
              exact Brocard.berndt_galway_chunk_0369 n m (by omega) (by omega) h
          · -- n >= 66366909
            exact Brocard.berndt_galway_chunk_0370 n m (by omega) (by omega) h
        · -- n >= 66546765
          rcases Nat.lt_or_ge n 66726621 with hs4 | hs4
          · -- n < 66726621
            exact Brocard.berndt_galway_chunk_0371 n m (by omega) (by omega) h
          · -- n >= 66726621
            exact Brocard.berndt_galway_chunk_0372 n m (by omega) (by omega) h
