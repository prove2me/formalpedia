-- Prove2me | solution 1 for Brocard.berndt_galway_group_094
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:29:07.350192+00:00
-- url     : https://prove2.me/submissions/2bba85cd-a790-4f70-bf13-2a1cf5371c33

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_4311
import Theorems.Thm_Brocard_berndt_galway_chunk_4312
import Theorems.Thm_Brocard_berndt_galway_chunk_4313
import Theorems.Thm_Brocard_berndt_galway_chunk_4314
import Theorems.Thm_Brocard_berndt_galway_chunk_4315
import Theorems.Thm_Brocard_berndt_galway_chunk_4316
import Theorems.Thm_Brocard_berndt_galway_chunk_4317
import Theorems.Thm_Brocard_berndt_galway_chunk_4318
import Theorems.Thm_Brocard_berndt_galway_chunk_4319
import Theorems.Thm_Brocard_berndt_galway_chunk_4320
import Theorems.Thm_Brocard_berndt_galway_chunk_4321
import Theorems.Thm_Brocard_berndt_galway_chunk_4322
import Theorems.Thm_Brocard_berndt_galway_chunk_4323
import Theorems.Thm_Brocard_berndt_galway_chunk_4324
import Theorems.Thm_Brocard_berndt_galway_chunk_4325
import Theorems.Thm_Brocard_berndt_galway_chunk_4326
import Theorems.Thm_Brocard_berndt_galway_chunk_4327
import Theorems.Thm_Brocard_berndt_galway_chunk_4328
import Theorems.Thm_Brocard_berndt_galway_chunk_4329
import Theorems.Thm_Brocard_berndt_galway_chunk_4330
import Theorems.Thm_Brocard_berndt_galway_chunk_4331
import Theorems.Thm_Brocard_berndt_galway_chunk_4332
import Theorems.Thm_Brocard_berndt_galway_chunk_4333
import Theorems.Thm_Brocard_berndt_galway_chunk_4334
import Theorems.Thm_Brocard_berndt_galway_chunk_4335
import Theorems.Thm_Brocard_berndt_galway_chunk_4336
import Theorems.Thm_Brocard_berndt_galway_chunk_4337
import Theorems.Thm_Brocard_berndt_galway_chunk_4338
import Theorems.Thm_Brocard_berndt_galway_chunk_4339
import Theorems.Thm_Brocard_berndt_galway_chunk_4340
import Theorems.Thm_Brocard_berndt_galway_chunk_4341
import Theorems.Thm_Brocard_berndt_galway_chunk_4342
import Theorems.Thm_Brocard_berndt_galway_chunk_4343
import Theorems.Thm_Brocard_berndt_galway_chunk_4344
import Theorems.Thm_Brocard_berndt_galway_chunk_4345
import Theorems.Thm_Brocard_berndt_galway_chunk_4346
import Theorems.Thm_Brocard_berndt_galway_chunk_4347
import Theorems.Thm_Brocard_berndt_galway_chunk_4348
import Theorems.Thm_Brocard_berndt_galway_chunk_4349
import Theorems.Thm_Brocard_berndt_galway_chunk_4350
import Theorems.Thm_Brocard_berndt_galway_chunk_4351
import Theorems.Thm_Brocard_berndt_galway_chunk_4352
import Theorems.Thm_Brocard_berndt_galway_chunk_4353
import Theorems.Thm_Brocard_berndt_galway_chunk_4354
import Theorems.Thm_Brocard_berndt_galway_chunk_4355
import Theorems.Thm_Brocard_berndt_galway_chunk_4356

theorem solution (n m : ℕ) (h1 : 775179856 ≤ n) (h2 : n < 783453237) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 779316546 with hs0 | hs0
  · -- n < 779316546
    rcases Nat.lt_or_ge n 777338129 with hs1 | hs1
    · -- n < 777338129
      rcases Nat.lt_or_ge n 776258992 with hs2 | hs2
      · -- n < 776258992
        rcases Nat.lt_or_ge n 775719424 with hs3 | hs3
        · -- n < 775719424
          rcases Nat.lt_or_ge n 775539568 with hs4 | hs4
          · -- n < 775539568
            rcases Nat.lt_or_ge n 775359712 with hs5 | hs5
            · -- n < 775359712
              exact Brocard.berndt_galway_chunk_4311 n m (by omega) (by omega) h
            · -- n >= 775359712
              exact Brocard.berndt_galway_chunk_4312 n m (by omega) (by omega) h
          · -- n >= 775539568
            exact Brocard.berndt_galway_chunk_4313 n m (by omega) (by omega) h
        · -- n >= 775719424
          rcases Nat.lt_or_ge n 776079136 with hs4 | hs4
          · -- n < 776079136
            rcases Nat.lt_or_ge n 775899280 with hs5 | hs5
            · -- n < 775899280
              exact Brocard.berndt_galway_chunk_4314 n m (by omega) (by omega) h
            · -- n >= 775899280
              exact Brocard.berndt_galway_chunk_4315 n m (by omega) (by omega) h
          · -- n >= 776079136
            exact Brocard.berndt_galway_chunk_4316 n m (by omega) (by omega) h
      · -- n >= 776258992
        rcases Nat.lt_or_ge n 776798561 with hs3 | hs3
        · -- n < 776798561
          rcases Nat.lt_or_ge n 776618705 with hs4 | hs4
          · -- n < 776618705
            rcases Nat.lt_or_ge n 776438848 with hs5 | hs5
            · -- n < 776438848
              exact Brocard.berndt_galway_chunk_4317 n m (by omega) (by omega) h
            · -- n >= 776438848
              exact Brocard.berndt_galway_chunk_4318 n m (by omega) (by omega) h
          · -- n >= 776618705
            exact Brocard.berndt_galway_chunk_4319 n m (by omega) (by omega) h
        · -- n >= 776798561
          rcases Nat.lt_or_ge n 777158273 with hs4 | hs4
          · -- n < 777158273
            rcases Nat.lt_or_ge n 776978417 with hs5 | hs5
            · -- n < 776978417
              exact Brocard.berndt_galway_chunk_4320 n m (by omega) (by omega) h
            · -- n >= 776978417
              exact Brocard.berndt_galway_chunk_4321 n m (by omega) (by omega) h
          · -- n >= 777158273
            exact Brocard.berndt_galway_chunk_4322 n m (by omega) (by omega) h
    · -- n >= 777338129
      rcases Nat.lt_or_ge n 778417266 with hs2 | hs2
      · -- n < 778417266
        rcases Nat.lt_or_ge n 777877697 with hs3 | hs3
        · -- n < 777877697
          rcases Nat.lt_or_ge n 777697841 with hs4 | hs4
          · -- n < 777697841
            rcases Nat.lt_or_ge n 777517985 with hs5 | hs5
            · -- n < 777517985
              exact Brocard.berndt_galway_chunk_4323 n m (by omega) (by omega) h
            · -- n >= 777517985
              exact Brocard.berndt_galway_chunk_4324 n m (by omega) (by omega) h
          · -- n >= 777697841
            exact Brocard.berndt_galway_chunk_4325 n m (by omega) (by omega) h
        · -- n >= 777877697
          rcases Nat.lt_or_ge n 778237410 with hs4 | hs4
          · -- n < 778237410
            rcases Nat.lt_or_ge n 778057553 with hs5 | hs5
            · -- n < 778057553
              exact Brocard.berndt_galway_chunk_4326 n m (by omega) (by omega) h
            · -- n >= 778057553
              exact Brocard.berndt_galway_chunk_4327 n m (by omega) (by omega) h
          · -- n >= 778237410
            exact Brocard.berndt_galway_chunk_4328 n m (by omega) (by omega) h
      · -- n >= 778417266
        rcases Nat.lt_or_ge n 778956834 with hs3 | hs3
        · -- n < 778956834
          rcases Nat.lt_or_ge n 778776978 with hs4 | hs4
          · -- n < 778776978
            rcases Nat.lt_or_ge n 778597122 with hs5 | hs5
            · -- n < 778597122
              exact Brocard.berndt_galway_chunk_4329 n m (by omega) (by omega) h
            · -- n >= 778597122
              exact Brocard.berndt_galway_chunk_4330 n m (by omega) (by omega) h
          · -- n >= 778776978
            exact Brocard.berndt_galway_chunk_4331 n m (by omega) (by omega) h
        · -- n >= 778956834
          rcases Nat.lt_or_ge n 779136690 with hs4 | hs4
          · -- n < 779136690
            exact Brocard.berndt_galway_chunk_4332 n m (by omega) (by omega) h
          · -- n >= 779136690
            exact Brocard.berndt_galway_chunk_4333 n m (by omega) (by omega) h
  · -- n >= 779316546
    rcases Nat.lt_or_ge n 781474820 with hs1 | hs1
    · -- n < 781474820
      rcases Nat.lt_or_ge n 780395683 with hs2 | hs2
      · -- n < 780395683
        rcases Nat.lt_or_ge n 779856115 with hs3 | hs3
        · -- n < 779856115
          rcases Nat.lt_or_ge n 779676258 with hs4 | hs4
          · -- n < 779676258
            rcases Nat.lt_or_ge n 779496402 with hs5 | hs5
            · -- n < 779496402
              exact Brocard.berndt_galway_chunk_4334 n m (by omega) (by omega) h
            · -- n >= 779496402
              exact Brocard.berndt_galway_chunk_4335 n m (by omega) (by omega) h
          · -- n >= 779676258
            exact Brocard.berndt_galway_chunk_4336 n m (by omega) (by omega) h
        · -- n >= 779856115
          rcases Nat.lt_or_ge n 780215827 with hs4 | hs4
          · -- n < 780215827
            rcases Nat.lt_or_ge n 780035971 with hs5 | hs5
            · -- n < 780035971
              exact Brocard.berndt_galway_chunk_4337 n m (by omega) (by omega) h
            · -- n >= 780035971
              exact Brocard.berndt_galway_chunk_4338 n m (by omega) (by omega) h
          · -- n >= 780215827
            exact Brocard.berndt_galway_chunk_4339 n m (by omega) (by omega) h
      · -- n >= 780395683
        rcases Nat.lt_or_ge n 780935251 with hs3 | hs3
        · -- n < 780935251
          rcases Nat.lt_or_ge n 780755395 with hs4 | hs4
          · -- n < 780755395
            rcases Nat.lt_or_ge n 780575539 with hs5 | hs5
            · -- n < 780575539
              exact Brocard.berndt_galway_chunk_4340 n m (by omega) (by omega) h
            · -- n >= 780575539
              exact Brocard.berndt_galway_chunk_4341 n m (by omega) (by omega) h
          · -- n >= 780755395
            exact Brocard.berndt_galway_chunk_4342 n m (by omega) (by omega) h
        · -- n >= 780935251
          rcases Nat.lt_or_ge n 781294964 with hs4 | hs4
          · -- n < 781294964
            rcases Nat.lt_or_ge n 781115107 with hs5 | hs5
            · -- n < 781115107
              exact Brocard.berndt_galway_chunk_4343 n m (by omega) (by omega) h
            · -- n >= 781115107
              exact Brocard.berndt_galway_chunk_4344 n m (by omega) (by omega) h
          · -- n >= 781294964
            exact Brocard.berndt_galway_chunk_4345 n m (by omega) (by omega) h
    · -- n >= 781474820
      rcases Nat.lt_or_ge n 782553956 with hs2 | hs2
      · -- n < 782553956
        rcases Nat.lt_or_ge n 782014388 with hs3 | hs3
        · -- n < 782014388
          rcases Nat.lt_or_ge n 781834532 with hs4 | hs4
          · -- n < 781834532
            rcases Nat.lt_or_ge n 781654676 with hs5 | hs5
            · -- n < 781654676
              exact Brocard.berndt_galway_chunk_4346 n m (by omega) (by omega) h
            · -- n >= 781654676
              exact Brocard.berndt_galway_chunk_4347 n m (by omega) (by omega) h
          · -- n >= 781834532
            exact Brocard.berndt_galway_chunk_4348 n m (by omega) (by omega) h
        · -- n >= 782014388
          rcases Nat.lt_or_ge n 782374100 with hs4 | hs4
          · -- n < 782374100
            rcases Nat.lt_or_ge n 782194244 with hs5 | hs5
            · -- n < 782194244
              exact Brocard.berndt_galway_chunk_4349 n m (by omega) (by omega) h
            · -- n >= 782194244
              exact Brocard.berndt_galway_chunk_4350 n m (by omega) (by omega) h
          · -- n >= 782374100
            exact Brocard.berndt_galway_chunk_4351 n m (by omega) (by omega) h
      · -- n >= 782553956
        rcases Nat.lt_or_ge n 783093525 with hs3 | hs3
        · -- n < 783093525
          rcases Nat.lt_or_ge n 782913669 with hs4 | hs4
          · -- n < 782913669
            rcases Nat.lt_or_ge n 782733812 with hs5 | hs5
            · -- n < 782733812
              exact Brocard.berndt_galway_chunk_4352 n m (by omega) (by omega) h
            · -- n >= 782733812
              exact Brocard.berndt_galway_chunk_4353 n m (by omega) (by omega) h
          · -- n >= 782913669
            exact Brocard.berndt_galway_chunk_4354 n m (by omega) (by omega) h
        · -- n >= 783093525
          rcases Nat.lt_or_ge n 783273381 with hs4 | hs4
          · -- n < 783273381
            exact Brocard.berndt_galway_chunk_4355 n m (by omega) (by omega) h
          · -- n >= 783273381
            exact Brocard.berndt_galway_chunk_4356 n m (by omega) (by omega) h
