-- Prove2me | solution 1 for Brocard.berndt_galway_group_009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:51:47.075197+00:00
-- url     : https://prove2.me/submissions/1fd9aa27-61fd-4e0b-9d75-48bf7e2f6267

import Mathlib.Data.Nat.Factorial.Basic
import Theorems.Thm_Brocard_berndt_galway_chunk_0373
import Theorems.Thm_Brocard_berndt_galway_chunk_0374
import Theorems.Thm_Brocard_berndt_galway_chunk_0375
import Theorems.Thm_Brocard_berndt_galway_chunk_0376
import Theorems.Thm_Brocard_berndt_galway_chunk_0377
import Theorems.Thm_Brocard_berndt_galway_chunk_0378
import Theorems.Thm_Brocard_berndt_galway_chunk_0379
import Theorems.Thm_Brocard_berndt_galway_chunk_0380
import Theorems.Thm_Brocard_berndt_galway_chunk_0381
import Theorems.Thm_Brocard_berndt_galway_chunk_0382
import Theorems.Thm_Brocard_berndt_galway_chunk_0383
import Theorems.Thm_Brocard_berndt_galway_chunk_0384
import Theorems.Thm_Brocard_berndt_galway_chunk_0385
import Theorems.Thm_Brocard_berndt_galway_chunk_0386
import Theorems.Thm_Brocard_berndt_galway_chunk_0387
import Theorems.Thm_Brocard_berndt_galway_chunk_0388
import Theorems.Thm_Brocard_berndt_galway_chunk_0389
import Theorems.Thm_Brocard_berndt_galway_chunk_0390
import Theorems.Thm_Brocard_berndt_galway_chunk_0391
import Theorems.Thm_Brocard_berndt_galway_chunk_0392
import Theorems.Thm_Brocard_berndt_galway_chunk_0393
import Theorems.Thm_Brocard_berndt_galway_chunk_0394
import Theorems.Thm_Brocard_berndt_galway_chunk_0395
import Theorems.Thm_Brocard_berndt_galway_chunk_0396
import Theorems.Thm_Brocard_berndt_galway_chunk_0397
import Theorems.Thm_Brocard_berndt_galway_chunk_0398
import Theorems.Thm_Brocard_berndt_galway_chunk_0399
import Theorems.Thm_Brocard_berndt_galway_chunk_0400
import Theorems.Thm_Brocard_berndt_galway_chunk_0401
import Theorems.Thm_Brocard_berndt_galway_chunk_0402
import Theorems.Thm_Brocard_berndt_galway_chunk_0403
import Theorems.Thm_Brocard_berndt_galway_chunk_0404
import Theorems.Thm_Brocard_berndt_galway_chunk_0405
import Theorems.Thm_Brocard_berndt_galway_chunk_0406
import Theorems.Thm_Brocard_berndt_galway_chunk_0407
import Theorems.Thm_Brocard_berndt_galway_chunk_0408
import Theorems.Thm_Brocard_berndt_galway_chunk_0409
import Theorems.Thm_Brocard_berndt_galway_chunk_0410
import Theorems.Thm_Brocard_berndt_galway_chunk_0411
import Theorems.Thm_Brocard_berndt_galway_chunk_0412
import Theorems.Thm_Brocard_berndt_galway_chunk_0413
import Theorems.Thm_Brocard_berndt_galway_chunk_0414
import Theorems.Thm_Brocard_berndt_galway_chunk_0415
import Theorems.Thm_Brocard_berndt_galway_chunk_0416
import Theorems.Thm_Brocard_berndt_galway_chunk_0417
import Theorems.Thm_Brocard_berndt_galway_chunk_0418

theorem solution (n m : ℕ) (h1 : 66906477 ≤ n) (h2 : n < 75179858) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  rcases Nat.lt_or_ge n 71043167 with hs0 | hs0
  · -- n < 71043167
    rcases Nat.lt_or_ge n 69064750 with hs1 | hs1
    · -- n < 69064750
      rcases Nat.lt_or_ge n 67985614 with hs2 | hs2
      · -- n < 67985614
        rcases Nat.lt_or_ge n 67446045 with hs3 | hs3
        · -- n < 67446045
          rcases Nat.lt_or_ge n 67266189 with hs4 | hs4
          · -- n < 67266189
            rcases Nat.lt_or_ge n 67086333 with hs5 | hs5
            · -- n < 67086333
              exact Brocard.berndt_galway_chunk_0373 n m (by omega) (by omega) h
            · -- n >= 67086333
              exact Brocard.berndt_galway_chunk_0374 n m (by omega) (by omega) h
          · -- n >= 67266189
            exact Brocard.berndt_galway_chunk_0375 n m (by omega) (by omega) h
        · -- n >= 67446045
          rcases Nat.lt_or_ge n 67805757 with hs4 | hs4
          · -- n < 67805757
            rcases Nat.lt_or_ge n 67625901 with hs5 | hs5
            · -- n < 67625901
              exact Brocard.berndt_galway_chunk_0376 n m (by omega) (by omega) h
            · -- n >= 67625901
              exact Brocard.berndt_galway_chunk_0377 n m (by omega) (by omega) h
          · -- n >= 67805757
            exact Brocard.berndt_galway_chunk_0378 n m (by omega) (by omega) h
      · -- n >= 67985614
        rcases Nat.lt_or_ge n 68525182 with hs3 | hs3
        · -- n < 68525182
          rcases Nat.lt_or_ge n 68345326 with hs4 | hs4
          · -- n < 68345326
            rcases Nat.lt_or_ge n 68165470 with hs5 | hs5
            · -- n < 68165470
              exact Brocard.berndt_galway_chunk_0379 n m (by omega) (by omega) h
            · -- n >= 68165470
              exact Brocard.berndt_galway_chunk_0380 n m (by omega) (by omega) h
          · -- n >= 68345326
            exact Brocard.berndt_galway_chunk_0381 n m (by omega) (by omega) h
        · -- n >= 68525182
          rcases Nat.lt_or_ge n 68884894 with hs4 | hs4
          · -- n < 68884894
            rcases Nat.lt_or_ge n 68705038 with hs5 | hs5
            · -- n < 68705038
              exact Brocard.berndt_galway_chunk_0382 n m (by omega) (by omega) h
            · -- n >= 68705038
              exact Brocard.berndt_galway_chunk_0383 n m (by omega) (by omega) h
          · -- n >= 68884894
            exact Brocard.berndt_galway_chunk_0384 n m (by omega) (by omega) h
    · -- n >= 69064750
      rcases Nat.lt_or_ge n 70143887 with hs2 | hs2
      · -- n < 70143887
        rcases Nat.lt_or_ge n 69604318 with hs3 | hs3
        · -- n < 69604318
          rcases Nat.lt_or_ge n 69424462 with hs4 | hs4
          · -- n < 69424462
            rcases Nat.lt_or_ge n 69244606 with hs5 | hs5
            · -- n < 69244606
              exact Brocard.berndt_galway_chunk_0385 n m (by omega) (by omega) h
            · -- n >= 69244606
              exact Brocard.berndt_galway_chunk_0386 n m (by omega) (by omega) h
          · -- n >= 69424462
            exact Brocard.berndt_galway_chunk_0387 n m (by omega) (by omega) h
        · -- n >= 69604318
          rcases Nat.lt_or_ge n 69964031 with hs4 | hs4
          · -- n < 69964031
            rcases Nat.lt_or_ge n 69784175 with hs5 | hs5
            · -- n < 69784175
              exact Brocard.berndt_galway_chunk_0388 n m (by omega) (by omega) h
            · -- n >= 69784175
              exact Brocard.berndt_galway_chunk_0389 n m (by omega) (by omega) h
          · -- n >= 69964031
            exact Brocard.berndt_galway_chunk_0390 n m (by omega) (by omega) h
      · -- n >= 70143887
        rcases Nat.lt_or_ge n 70683455 with hs3 | hs3
        · -- n < 70683455
          rcases Nat.lt_or_ge n 70503599 with hs4 | hs4
          · -- n < 70503599
            rcases Nat.lt_or_ge n 70323743 with hs5 | hs5
            · -- n < 70323743
              exact Brocard.berndt_galway_chunk_0391 n m (by omega) (by omega) h
            · -- n >= 70323743
              exact Brocard.berndt_galway_chunk_0392 n m (by omega) (by omega) h
          · -- n >= 70503599
            exact Brocard.berndt_galway_chunk_0393 n m (by omega) (by omega) h
        · -- n >= 70683455
          rcases Nat.lt_or_ge n 70863311 with hs4 | hs4
          · -- n < 70863311
            exact Brocard.berndt_galway_chunk_0394 n m (by omega) (by omega) h
          · -- n >= 70863311
            exact Brocard.berndt_galway_chunk_0395 n m (by omega) (by omega) h
  · -- n >= 71043167
    rcases Nat.lt_or_ge n 73201440 with hs1 | hs1
    · -- n < 73201440
      rcases Nat.lt_or_ge n 72122304 with hs2 | hs2
      · -- n < 72122304
        rcases Nat.lt_or_ge n 71582736 with hs3 | hs3
        · -- n < 71582736
          rcases Nat.lt_or_ge n 71402879 with hs4 | hs4
          · -- n < 71402879
            rcases Nat.lt_or_ge n 71223023 with hs5 | hs5
            · -- n < 71223023
              exact Brocard.berndt_galway_chunk_0396 n m (by omega) (by omega) h
            · -- n >= 71223023
              exact Brocard.berndt_galway_chunk_0397 n m (by omega) (by omega) h
          · -- n >= 71402879
            exact Brocard.berndt_galway_chunk_0398 n m (by omega) (by omega) h
        · -- n >= 71582736
          rcases Nat.lt_or_ge n 71942448 with hs4 | hs4
          · -- n < 71942448
            rcases Nat.lt_or_ge n 71762592 with hs5 | hs5
            · -- n < 71762592
              exact Brocard.berndt_galway_chunk_0399 n m (by omega) (by omega) h
            · -- n >= 71762592
              exact Brocard.berndt_galway_chunk_0400 n m (by omega) (by omega) h
          · -- n >= 71942448
            exact Brocard.berndt_galway_chunk_0401 n m (by omega) (by omega) h
      · -- n >= 72122304
        rcases Nat.lt_or_ge n 72661872 with hs3 | hs3
        · -- n < 72661872
          rcases Nat.lt_or_ge n 72482016 with hs4 | hs4
          · -- n < 72482016
            rcases Nat.lt_or_ge n 72302160 with hs5 | hs5
            · -- n < 72302160
              exact Brocard.berndt_galway_chunk_0402 n m (by omega) (by omega) h
            · -- n >= 72302160
              exact Brocard.berndt_galway_chunk_0403 n m (by omega) (by omega) h
          · -- n >= 72482016
            exact Brocard.berndt_galway_chunk_0404 n m (by omega) (by omega) h
        · -- n >= 72661872
          rcases Nat.lt_or_ge n 73021584 with hs4 | hs4
          · -- n < 73021584
            rcases Nat.lt_or_ge n 72841728 with hs5 | hs5
            · -- n < 72841728
              exact Brocard.berndt_galway_chunk_0405 n m (by omega) (by omega) h
            · -- n >= 72841728
              exact Brocard.berndt_galway_chunk_0406 n m (by omega) (by omega) h
          · -- n >= 73021584
            exact Brocard.berndt_galway_chunk_0407 n m (by omega) (by omega) h
    · -- n >= 73201440
      rcases Nat.lt_or_ge n 74280577 with hs2 | hs2
      · -- n < 74280577
        rcases Nat.lt_or_ge n 73741009 with hs3 | hs3
        · -- n < 73741009
          rcases Nat.lt_or_ge n 73561153 with hs4 | hs4
          · -- n < 73561153
            rcases Nat.lt_or_ge n 73381297 with hs5 | hs5
            · -- n < 73381297
              exact Brocard.berndt_galway_chunk_0408 n m (by omega) (by omega) h
            · -- n >= 73381297
              exact Brocard.berndt_galway_chunk_0409 n m (by omega) (by omega) h
          · -- n >= 73561153
            exact Brocard.berndt_galway_chunk_0410 n m (by omega) (by omega) h
        · -- n >= 73741009
          rcases Nat.lt_or_ge n 74100721 with hs4 | hs4
          · -- n < 74100721
            rcases Nat.lt_or_ge n 73920865 with hs5 | hs5
            · -- n < 73920865
              exact Brocard.berndt_galway_chunk_0411 n m (by omega) (by omega) h
            · -- n >= 73920865
              exact Brocard.berndt_galway_chunk_0412 n m (by omega) (by omega) h
          · -- n >= 74100721
            exact Brocard.berndt_galway_chunk_0413 n m (by omega) (by omega) h
      · -- n >= 74280577
        rcases Nat.lt_or_ge n 74820145 with hs3 | hs3
        · -- n < 74820145
          rcases Nat.lt_or_ge n 74640289 with hs4 | hs4
          · -- n < 74640289
            rcases Nat.lt_or_ge n 74460433 with hs5 | hs5
            · -- n < 74460433
              exact Brocard.berndt_galway_chunk_0414 n m (by omega) (by omega) h
            · -- n >= 74460433
              exact Brocard.berndt_galway_chunk_0415 n m (by omega) (by omega) h
          · -- n >= 74640289
            exact Brocard.berndt_galway_chunk_0416 n m (by omega) (by omega) h
        · -- n >= 74820145
          rcases Nat.lt_or_ge n 75000002 with hs4 | hs4
          · -- n < 75000002
            exact Brocard.berndt_galway_chunk_0417 n m (by omega) (by omega) h
          · -- n >= 75000002
            exact Brocard.berndt_galway_chunk_0418 n m (by omega) (by omega) h
