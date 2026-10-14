-- Prove2me | solution 1 for DbarRegularity.hormander_of_norm_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T14:55:40.69733+00:00
-- url     : https://prove2.me/submissions/113f04d5-8585-4732-9053-6b593701182b

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_DbarRegularity_lintegral_inv_norm_pow_succ_le
import Mathlib.Analysis.Calculus.MeanValue



namespace DbarRegularity

open MeasureTheory Set
open scoped ENNReal ContDiff

/-- A kernel that is `C¹` off the origin with `|∇K(x)| ≤ B / |x|^{d+1}` satisfies the Hörmander
condition `∫_{|x| ≥ 2|y|} |K(x - y) - K(x)| dx ≤ C B`, with `C` depending only on `d`. -/
theorem hormander_of_norm_fderiv_le (d : ℕ) :
    ∃ C : ℝ, ∀ (B : ℝ) (K : EuclideanSpace ℝ (Fin d) → ℂ),
      ContDiffOn ℝ 1 K {0}ᶜ →
      (∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ B / ‖x‖ ^ (d + 1)) →
      ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal (C * B) := by
  obtain ⟨C₀, hC₀⟩ := lintegral_inv_norm_pow_succ_le d
  refine ⟨2 ^ d * C₀, fun B K hK hD y hy => ?_⟩
  have hy0 : 0 < ‖y‖ := norm_pos_iff.mpr hy
  -- pointwise bound
  have hpt : ∀ x ∈ {x : EuclideanSpace ℝ (Fin d) | 2 * ‖y‖ ≤ ‖x‖},
      ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal (2 ^ (d + 1) * B * ‖y‖) *
        ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹) := by
    intro x hx
    simp only [mem_setOf_eq] at hx
    have hx0 : 0 < ‖x‖ := by linarith
    have hxne : x ≠ 0 := norm_pos_iff.mp hx0
    have hB : 0 ≤ B := by
      have h1 := hD x hxne
      have h2 : 0 ≤ B / ‖x‖ ^ (d + 1) := (norm_nonneg _).trans h1
      exact (div_nonneg_iff.mp h2).elim (fun h => h.1) (fun h => by
        exfalso; have := h.2; have : 0 < ‖x‖ ^ (d + 1) := by positivity
        linarith)
    -- points of the segment stay at distance ≥ |x|/2 from 0
    have hseg : ∀ z ∈ segment ℝ x (x - y), ‖x‖ / 2 ≤ ‖z‖ := by
      intro z hz
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      have : a • x + b • (x - y) = x - b • y := by
        rw [smul_sub, ← add_sub_assoc, ← add_smul, hab, one_smul]
      rw [this]
      have h1 : ‖b • y‖ ≤ ‖y‖ := by
        rw [norm_smul, Real.norm_of_nonneg hb]
        nlinarith
      have h2 := norm_sub_norm_le x (b • y)
      linarith
    have hdiff : ∀ z ∈ segment ℝ x (x - y), DifferentiableAt ℝ K z := by
      intro z hz
      have hz0 : z ≠ 0 := by
        have := hseg z hz
        exact norm_pos_iff.mp (by linarith)
      exact (hK.differentiableOn (by norm_num) z hz0).differentiableAt
        (isOpen_compl_singleton.mem_nhds hz0)
    have hbound : ∀ z ∈ segment ℝ x (x - y), ‖fderiv ℝ K z‖ ≤ B / (‖x‖ / 2) ^ (d + 1) := by
      intro z hz
      have hz := hseg z hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp (by linarith)
      refine (hD z hz0).trans ?_
      exact div_le_div_of_nonneg_left hB (by positivity) (pow_le_pow_left₀ (by positivity) hz _)
    have hmv := (convex_segment x (x - y)).norm_image_sub_le_of_norm_fderiv_le hdiff hbound
      (left_mem_segment ℝ x (x - y)) (right_mem_segment ℝ x (x - y))
    rw [sub_sub_cancel_left, norm_neg] at hmv
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (hmv.trans (le_of_eq ?_))
    rw [div_pow]; field_simp
  calc ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ
      ≤ ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ENNReal.ofReal (2 ^ (d + 1) * B * ‖y‖) *
          ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹) :=
        setLIntegral_mono' (measurableSet_le measurable_const measurable_norm) hpt
    _ = ENNReal.ofReal (2 ^ (d + 1) * B * ‖y‖) *
          ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ENNReal.ofReal ((‖x‖ ^ (d + 1))⁻¹) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (2 ^ (d + 1) * B * ‖y‖) * ENNReal.ofReal (C₀ / (2 * ‖y‖)) := by
        gcongr; exact hC₀ _ (by positivity)
    _ ≤ ENNReal.ofReal (2 ^ d * C₀ * B) := by
        rcases le_or_gt 0 B with hB | hB
        · rw [← ENNReal.ofReal_mul (by positivity)]
          apply le_of_eq; congr 1; field_simp; ring
        · rw [ENNReal.ofReal_of_nonpos (p := 2 ^ (d + 1) * B * ‖y‖)
            (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by positivity) hB.le)
              hy0.le), zero_mul]
          exact zero_le'

end DbarRegularity

open DbarRegularity

open MeasureTheory Set
open scoped ENNReal ContDiff

theorem solution (d : ℕ) :
    ∃ C : ℝ, ∀ (B : ℝ) (K : EuclideanSpace ℝ (Fin d) → ℂ),
      ContDiffOn ℝ 1 K {0}ᶜ →
      (∀ x, x ≠ 0 → ‖fderiv ℝ K x‖ ≤ B / ‖x‖ ^ (d + 1)) →
      ∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal (C * B) :=
  hormander_of_norm_fderiv_le d
