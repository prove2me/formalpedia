-- Prove2me | solution 1 for Conway99Formal.OrdinaryRank.rank33_score_gluing_bound
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T01:47:33.595757+00:00
-- url     : https://prove2.me/submissions/eb2e4041-5ae3-499f-87a8-1ec35f99a15a

import Definitions.Def_Conway99_OrdinaryRank_Rank33Gluing_20261004

set_option autoImplicit false

theorem solution (s j : ℕ) (d detC0 : ℚ)
    (hs : s ≤ 2) (hj : j ≤ 2 ^ s) (hd : 0 ≤ d)
    (hdet : detC0 * 14 ^ s = d * 7 ^ 9 * (j : ℚ) ^ 2) :
    detC0 ≤ (2 / 7 : ℚ) ^ s * d * 7 ^ 9 := by
  have hjq : (j : ℚ) ≤ (2 : ℚ) ^ s := by exact_mod_cast hj
  have hjnonneg : (0 : ℚ) ≤ j := by positivity
  have htwo : (0 : ℚ) ≤ (2 : ℚ) ^ s := by positivity
  have hjsq : (j : ℚ) ^ 2 ≤ ((2 : ℚ) ^ s) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hjq) (add_nonneg htwo hjnonneg)]
  have hmul := mul_le_mul_of_nonneg_left hjsq
    (mul_nonneg hd (by positivity : (0 : ℚ) ≤ 7 ^ 9))
  interval_cases s <;> norm_num at hdet hmul ⊢ <;> nlinarith

#print axioms solution
