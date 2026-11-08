-- Prove2me | solution 1 for DeltaSLearning.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:42:17.967903+00:00
-- url     : https://prove2.me/submissions/c7d8a5c6-9dce-4a9f-87d7-c8b2e05abd37

import Mathlib
import Definitions.Def_DeltaSLearning_pseudoCost
import Definitions.Def_DeltaSLearning_gamma

open DeltaSLearning in
theorem solution (cp : DeltaSLearning.Params) (x y d : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ cp.β)
    (hd : 0 ≤ d) : |DeltaSLearning.pseudoCost cp x y d| ≤ DeltaSLearning.gamma cp := by
  have hp : 0 < cp.p := lt_of_le_of_lt cp.c_nonneg cp.c_lt_p
  have hI : 0 ≤ (if x < y then (1:ℝ) else 0) ∧ (if x < y then (1:ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have hM1 : 0 ≤ max (y - d) 0 := le_max_right _ _
  have hM2 : max (y - d) 0 ≤ cp.β := max_le (by linarith) (by linarith)
  have hm1 : 0 ≤ min y d := le_min (by linarith) hd
  have hm2 : min y d ≤ cp.β := (min_le_left _ _).trans hy
  have a1 := mul_le_mul_of_nonneg_left hI.2 cp.K_pos.le
  have a2 := mul_nonneg cp.K_pos.le hI.1
  have a3 := mul_le_mul_of_nonneg_left (by linarith : y - x ≤ cp.β) cp.c_nonneg
  have a4 := mul_nonneg cp.c_nonneg (sub_nonneg.2 hxy)
  have a5 := mul_le_mul_of_nonneg_left hM2 cp.h_pos.le
  have a6 := mul_nonneg cp.h_pos.le hM1
  have a7 := mul_le_mul_of_nonneg_left hm2 hp.le
  have a8 := mul_nonneg hp.le hm1
  have hb : 0 ≤ cp.β := by linarith
  have a9 := mul_nonneg cp.c_nonneg hb
  have a10 := mul_nonneg cp.h_pos.le hb
  have a11 := mul_nonneg hp.le hb
  unfold DeltaSLearning.pseudoCost DeltaSLearning.gamma
  rw [abs_le]
  constructor <;> nlinarith
