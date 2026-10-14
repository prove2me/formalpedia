-- Prove2me | solution 1 for DbarRegularity.norm_inv_norm_smul_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:29:21.746994+00:00
-- url     : https://prove2.me/submissions/38b1ed6a-b499-463b-a191-458d506afe06

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real



namespace DbarRegularity

/-- Distance between the radial projections to the unit sphere: for `v ≠ 0`,
`|u/|u| - v/|v|| ≤ 2 |u - v| / |v|` (with `0/|0| = 0`). -/
theorem norm_inv_norm_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (hv : v ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ 2 * ‖u - v‖ / ‖v‖ := by
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  by_cases hu : u = 0
  · subst hu
    simp only [norm_zero, inv_zero, smul_zero, zero_sub, norm_neg, norm_smul, norm_inv,
      norm_norm, inv_mul_cancel₀ hv0.ne']
    rw [le_div_iff₀ hv0]; linarith
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have h1 : ‖u‖⁻¹ • u - ‖v‖⁻¹ • v = ‖v‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • u := by
    rw [smul_sub, sub_smul]; abel
  have h2 : |‖u‖⁻¹ - ‖v‖⁻¹| * ‖u‖ = |‖v‖ - ‖u‖| / ‖v‖ := by
    have h3 : (‖u‖⁻¹ - ‖v‖⁻¹) * ‖u‖ = (‖v‖ - ‖u‖) / ‖v‖ := by field_simp
    rw [show |‖u‖⁻¹ - ‖v‖⁻¹| * ‖u‖ = |(‖u‖⁻¹ - ‖v‖⁻¹) * ‖u‖| by rw [abs_mul, abs_of_pos hu0],
      h3, abs_div, abs_of_pos hv0]
  rw [h1]
  calc ‖‖v‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • u‖
      ≤ ‖‖v‖⁻¹ • (u - v)‖ + ‖(‖u‖⁻¹ - ‖v‖⁻¹) • u‖ := norm_add_le _ _
    _ = ‖u - v‖ / ‖v‖ + |‖v‖ - ‖u‖| / ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv, abs_of_pos hv0,
          h2, inv_mul_eq_div]
    _ ≤ ‖u - v‖ / ‖v‖ + ‖u - v‖ / ‖v‖ := by
        gcongr
        rw [norm_sub_rev]; exact abs_norm_sub_norm_le v u
    _ = 2 * ‖u - v‖ / ‖v‖ := by ring

end DbarRegularity

open DbarRegularity

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v : E) (hv : v ≠ 0) :
    ‖‖u‖⁻¹ • u - ‖v‖⁻¹ • v‖ ≤ 2 * ‖u - v‖ / ‖v‖ :=
  norm_inv_norm_smul_sub_le u v hv
