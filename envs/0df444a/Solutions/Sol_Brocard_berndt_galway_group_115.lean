-- Prove2me | solution 1 for Brocard.berndt_galway_group_115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:36:28.198507+00:00
-- url     : https://prove2.me/submissions/44737048-c9aa-42cd-8a6a-dffe11cb19bf

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_5285
import Theorems.Thm_Brocard_berndt_galway_chunk_5286
import Theorems.Thm_Brocard_berndt_galway_chunk_5287
import Theorems.Thm_Brocard_berndt_galway_chunk_5288
import Theorems.Thm_Brocard_berndt_galway_chunk_5289
import Theorems.Thm_Brocard_berndt_galway_chunk_5290
import Theorems.Thm_Brocard_berndt_galway_chunk_5291
import Theorems.Thm_Brocard_berndt_galway_chunk_5292
import Theorems.Thm_Brocard_berndt_galway_chunk_5293
import Theorems.Thm_Brocard_berndt_galway_chunk_5294
import Theorems.Thm_Brocard_berndt_galway_chunk_5295
import Theorems.Thm_Brocard_berndt_galway_chunk_5296
import Theorems.Thm_Brocard_berndt_galway_chunk_5297
import Theorems.Thm_Brocard_berndt_galway_chunk_5298
import Theorems.Thm_Brocard_berndt_galway_chunk_5299
import Theorems.Thm_Brocard_berndt_galway_chunk_5300
import Theorems.Thm_Brocard_berndt_galway_chunk_5301
import Theorems.Thm_Brocard_berndt_galway_chunk_5302
import Theorems.Thm_Brocard_berndt_galway_chunk_5303
import Theorems.Thm_Brocard_berndt_galway_chunk_5304
import Theorems.Thm_Brocard_berndt_galway_chunk_5305
import Theorems.Thm_Brocard_berndt_galway_chunk_5306
import Theorems.Thm_Brocard_berndt_galway_chunk_5307
import Theorems.Thm_Brocard_berndt_galway_chunk_5308
import Theorems.Thm_Brocard_berndt_galway_chunk_5309
import Theorems.Thm_Brocard_berndt_galway_chunk_5310
import Theorems.Thm_Brocard_berndt_galway_chunk_5311
import Theorems.Thm_Brocard_berndt_galway_chunk_5312
import Theorems.Thm_Brocard_berndt_galway_chunk_5313
import Theorems.Thm_Brocard_berndt_galway_chunk_5314
import Theorems.Thm_Brocard_berndt_galway_chunk_5315
import Theorems.Thm_Brocard_berndt_galway_chunk_5316
import Theorems.Thm_Brocard_berndt_galway_chunk_5317
import Theorems.Thm_Brocard_berndt_galway_chunk_5318
import Theorems.Thm_Brocard_berndt_galway_chunk_5319
import Theorems.Thm_Brocard_berndt_galway_chunk_5320
import Theorems.Thm_Brocard_berndt_galway_chunk_5321
import Theorems.Thm_Brocard_berndt_galway_chunk_5322
import Theorems.Thm_Brocard_berndt_galway_chunk_5323
import Theorems.Thm_Brocard_berndt_galway_chunk_5324
import Theorems.Thm_Brocard_berndt_galway_chunk_5325
import Theorems.Thm_Brocard_berndt_galway_chunk_5326
import Theorems.Thm_Brocard_berndt_galway_chunk_5327
import Theorems.Thm_Brocard_berndt_galway_chunk_5328
import Theorems.Thm_Brocard_berndt_galway_chunk_5329
import Theorems.Thm_Brocard_berndt_galway_chunk_5330

theorem solution (n m : ℕ) (h1 : 950359712 ≤ n) (h2 : n < 958633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 954496402 with hs0 | hs0
  · -- n < 954496402
    rcases Nat.lt_or_ge n 952517985 with hs1 | hs1
    · -- n < 952517985
      rcases Nat.lt_or_ge n 951438848 with hs2 | hs2
      · -- n < 951438848
        rcases Nat.lt_or_ge n 950899280 with hs3 | hs3
        · -- n < 950899280
          rcases Nat.lt_or_ge n 950719424 with hs4 | hs4
          · -- n < 950719424
            rcases Nat.lt_or_ge n 950539568 with hs5 | hs5
            · -- n < 950539568
              exact Brocard.berndt_galway_chunk_5285 n m (by omega) (by omega) h
            · -- n >= 950539568
              exact Brocard.berndt_galway_chunk_5286 n m (by omega) (by omega) h
          · -- n >= 950719424
            exact Brocard.berndt_galway_chunk_5287 n m (by omega) (by omega) h
        · -- n >= 950899280
          rcases Nat.lt_or_ge n 951258992 with hs4 | hs4
          · -- n < 951258992
            rcases Nat.lt_or_ge n 951079136 with hs5 | hs5
            · -- n < 951079136
              exact Brocard.berndt_galway_chunk_5288 n m (by omega) (by omega) h
            · -- n >= 951079136
              exact Brocard.berndt_galway_chunk_5289 n m (by omega) (by omega) h
          · -- n >= 951258992
            exact Brocard.berndt_galway_chunk_5290 n m (by omega) (by omega) h
      · -- n >= 951438848
        rcases Nat.lt_or_ge n 951978417 with hs3 | hs3
        · -- n < 951978417
          rcases Nat.lt_or_ge n 951798561 with hs4 | hs4
          · -- n < 951798561
            rcases Nat.lt_or_ge n 951618705 with hs5 | hs5
            · -- n < 951618705
              exact Brocard.berndt_galway_chunk_5291 n m (by omega) (by omega) h
            · -- n >= 951618705
              exact Brocard.berndt_galway_chunk_5292 n m (by omega) (by omega) h
          · -- n >= 951798561
            exact Brocard.berndt_galway_chunk_5293 n m (by omega) (by omega) h
        · -- n >= 951978417
          rcases Nat.lt_or_ge n 952338129 with hs4 | hs4
          · -- n < 952338129
            rcases Nat.lt_or_ge n 952158273 with hs5 | hs5
            · -- n < 952158273
              exact Brocard.berndt_galway_chunk_5294 n m (by omega) (by omega) h
            · -- n >= 952158273
              exact Brocard.berndt_galway_chunk_5295 n m (by omega) (by omega) h
          · -- n >= 952338129
            exact Brocard.berndt_galway_chunk_5296 n m (by omega) (by omega) h
    · -- n >= 952517985
      rcases Nat.lt_or_ge n 953597122 with hs2 | hs2
      · -- n < 953597122
        rcases Nat.lt_or_ge n 953057553 with hs3 | hs3
        · -- n < 953057553
          rcases Nat.lt_or_ge n 952877697 with hs4 | hs4
          · -- n < 952877697
            rcases Nat.lt_or_ge n 952697841 with hs5 | hs5
            · -- n < 952697841
              exact Brocard.berndt_galway_chunk_5297 n m (by omega) (by omega) h
            · -- n >= 952697841
              exact Brocard.berndt_galway_chunk_5298 n m (by omega) (by omega) h
          · -- n >= 952877697
            exact Brocard.berndt_galway_chunk_5299 n m (by omega) (by omega) h
        · -- n >= 953057553
          rcases Nat.lt_or_ge n 953417266 with hs4 | hs4
          · -- n < 953417266
            rcases Nat.lt_or_ge n 953237410 with hs5 | hs5
            · -- n < 953237410
              exact Brocard.berndt_galway_chunk_5300 n m (by omega) (by omega) h
            · -- n >= 953237410
              exact Brocard.berndt_galway_chunk_5301 n m (by omega) (by omega) h
          · -- n >= 953417266
            exact Brocard.berndt_galway_chunk_5302 n m (by omega) (by omega) h
      · -- n >= 953597122
        rcases Nat.lt_or_ge n 954136690 with hs3 | hs3
        · -- n < 954136690
          rcases Nat.lt_or_ge n 953956834 with hs4 | hs4
          · -- n < 953956834
            rcases Nat.lt_or_ge n 953776978 with hs5 | hs5
            · -- n < 953776978
              exact Brocard.berndt_galway_chunk_5303 n m (by omega) (by omega) h
            · -- n >= 953776978
              exact Brocard.berndt_galway_chunk_5304 n m (by omega) (by omega) h
          · -- n >= 953956834
            exact Brocard.berndt_galway_chunk_5305 n m (by omega) (by omega) h
        · -- n >= 954136690
          rcases Nat.lt_or_ge n 954316546 with hs4 | hs4
          · -- n < 954316546
            exact Brocard.berndt_galway_chunk_5306 n m (by omega) (by omega) h
          · -- n >= 954316546
            exact Brocard.berndt_galway_chunk_5307 n m (by omega) (by omega) h
  · -- n >= 954496402
    rcases Nat.lt_or_ge n 956654676 with hs1 | hs1
    · -- n < 956654676
      rcases Nat.lt_or_ge n 955575539 with hs2 | hs2
      · -- n < 955575539
        rcases Nat.lt_or_ge n 955035971 with hs3 | hs3
        · -- n < 955035971
          rcases Nat.lt_or_ge n 954856115 with hs4 | hs4
          · -- n < 954856115
            rcases Nat.lt_or_ge n 954676258 with hs5 | hs5
            · -- n < 954676258
              exact Brocard.berndt_galway_chunk_5308 n m (by omega) (by omega) h
            · -- n >= 954676258
              exact Brocard.berndt_galway_chunk_5309 n m (by omega) (by omega) h
          · -- n >= 954856115
            exact Brocard.berndt_galway_chunk_5310 n m (by omega) (by omega) h
        · -- n >= 955035971
          rcases Nat.lt_or_ge n 955395683 with hs4 | hs4
          · -- n < 955395683
            rcases Nat.lt_or_ge n 955215827 with hs5 | hs5
            · -- n < 955215827
              exact Brocard.berndt_galway_chunk_5311 n m (by omega) (by omega) h
            · -- n >= 955215827
              exact Brocard.berndt_galway_chunk_5312 n m (by omega) (by omega) h
          · -- n >= 955395683
            exact Brocard.berndt_galway_chunk_5313 n m (by omega) (by omega) h
      · -- n >= 955575539
        rcases Nat.lt_or_ge n 956115107 with hs3 | hs3
        · -- n < 956115107
          rcases Nat.lt_or_ge n 955935251 with hs4 | hs4
          · -- n < 955935251
            rcases Nat.lt_or_ge n 955755395 with hs5 | hs5
            · -- n < 955755395
              exact Brocard.berndt_galway_chunk_5314 n m (by omega) (by omega) h
            · -- n >= 955755395
              exact Brocard.berndt_galway_chunk_5315 n m (by omega) (by omega) h
          · -- n >= 955935251
            exact Brocard.berndt_galway_chunk_5316 n m (by omega) (by omega) h
        · -- n >= 956115107
          rcases Nat.lt_or_ge n 956474820 with hs4 | hs4
          · -- n < 956474820
            rcases Nat.lt_or_ge n 956294964 with hs5 | hs5
            · -- n < 956294964
              exact Brocard.berndt_galway_chunk_5317 n m (by omega) (by omega) h
            · -- n >= 956294964
              exact Brocard.berndt_galway_chunk_5318 n m (by omega) (by omega) h
          · -- n >= 956474820
            exact Brocard.berndt_galway_chunk_5319 n m (by omega) (by omega) h
    · -- n >= 956654676
      rcases Nat.lt_or_ge n 957733812 with hs2 | hs2
      · -- n < 957733812
        rcases Nat.lt_or_ge n 957194244 with hs3 | hs3
        · -- n < 957194244
          rcases Nat.lt_or_ge n 957014388 with hs4 | hs4
          · -- n < 957014388
            rcases Nat.lt_or_ge n 956834532 with hs5 | hs5
            · -- n < 956834532
              exact Brocard.berndt_galway_chunk_5320 n m (by omega) (by omega) h
            · -- n >= 956834532
              exact Brocard.berndt_galway_chunk_5321 n m (by omega) (by omega) h
          · -- n >= 957014388
            exact Brocard.berndt_galway_chunk_5322 n m (by omega) (by omega) h
        · -- n >= 957194244
          rcases Nat.lt_or_ge n 957553956 with hs4 | hs4
          · -- n < 957553956
            rcases Nat.lt_or_ge n 957374100 with hs5 | hs5
            · -- n < 957374100
              exact Brocard.berndt_galway_chunk_5323 n m (by omega) (by omega) h
            · -- n >= 957374100
              exact Brocard.berndt_galway_chunk_5324 n m (by omega) (by omega) h
          · -- n >= 957553956
            exact Brocard.berndt_galway_chunk_5325 n m (by omega) (by omega) h
      · -- n >= 957733812
        rcases Nat.lt_or_ge n 958273381 with hs3 | hs3
        · -- n < 958273381
          rcases Nat.lt_or_ge n 958093525 with hs4 | hs4
          · -- n < 958093525
            rcases Nat.lt_or_ge n 957913669 with hs5 | hs5
            · -- n < 957913669
              exact Brocard.berndt_galway_chunk_5326 n m (by omega) (by omega) h
            · -- n >= 957913669
              exact Brocard.berndt_galway_chunk_5327 n m (by omega) (by omega) h
          · -- n >= 958093525
            exact Brocard.berndt_galway_chunk_5328 n m (by omega) (by omega) h
        · -- n >= 958273381
          rcases Nat.lt_or_ge n 958453237 with hs4 | hs4
          · -- n < 958453237
            exact Brocard.berndt_galway_chunk_5329 n m (by omega) (by omega) h
          · -- n >= 958453237
            exact Brocard.berndt_galway_chunk_5330 n m (by omega) (by omega) h
