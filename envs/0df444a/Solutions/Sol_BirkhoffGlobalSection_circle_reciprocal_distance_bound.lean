-- Prove2me | solution 1 for BirkhoffGlobalSection.circle_reciprocal_distance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T07:35:34.05819+00:00
-- url     : https://prove2.me/submissions/368f260e-8fb1-4bc3-b749-8e772c846743

import Mathlib

theorem solution (r a : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (ha_lo : -r ≤ a) (ha_hi : a ≤ r) :
    r - a ≤ 1 / (1 - r) -
      1 / Real.sqrt (1 + r ^ 2 - 2 * a) := by
  let d : ℝ := Real.sqrt (1 + r ^ 2 - 2 * a)
  have hbase : 0 < 1 - r := by linarith
  have hrad : 0 < 1 + r ^ 2 - 2 * a := by
    nlinarith [sq_pos_of_pos hbase]
  have hdsq : d ^ 2 = 1 + r ^ 2 - 2 * a := Real.sq_sqrt (le_of_lt hrad)
  have hdpos : 0 < d := Real.sqrt_pos.2 hrad
  have hlo : 1 - r ≤ d := by
    by_contra h
    have hlt : d < 1 - r := lt_of_not_ge h
    nlinarith [mul_pos (sub_pos.mpr hlt) (add_pos hdpos hbase)]
  have hhi : d ≤ 1 + r := by
    by_contra h
    have hgt : 1 + r < d := lt_of_not_ge h
    have hp : 0 < 1 + r := by linarith
    nlinarith [mul_pos (sub_pos.mpr hgt) (add_pos hdpos hp)]
  have hbd : (1 - r) * d ≤ 1 := by
    have hm := mul_le_mul_of_nonneg_left hhi (le_of_lt hbase)
    nlinarith [sq_nonneg r]
  have hsum : d + (1 - r) ≤ 2 := by linarith
  have hprod : (1 - r) * d * (d + (1 - r)) ≤ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsum
      (le_of_lt (mul_pos hbase hdpos))
    nlinarith
  have hfrac : 1 / (1 - r) - 1 / d -
      (d ^ 2 - (1 - r) ^ 2) / 2 =
      (d - (1 - r)) * (2 - (1 - r) * d * (d + (1 - r))) /
        (2 * (1 - r) * d) := by
    have hbne : 1 - r ≠ 0 := ne_of_gt hbase
    have hdne : d ≠ 0 := ne_of_gt hdpos
    field_simp <;> ring
  have hnon : 0 ≤
      (d - (1 - r)) * (2 - (1 - r) * d * (d + (1 - r))) /
        (2 * (1 - r) * d) := by
    apply div_nonneg
    · exact mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hprod)
    · exact le_of_lt (mul_pos (mul_pos (by norm_num) hbase) hdpos)
  have ht : r - a = (d ^ 2 - (1 - r) ^ 2) / 2 := by
    nlinarith [hdsq]
  change r - a ≤ 1 / (1 - r) - 1 / d
  linarith
