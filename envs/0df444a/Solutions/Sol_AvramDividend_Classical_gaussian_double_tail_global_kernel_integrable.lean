-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_global_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T12:16:45.31232+00:00
-- url     : https://prove2.me/submissions/eba92c1b-fd63-4922-97ff-4dcd6c42650b

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_tonelli
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_full_lintegral
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_damped_quadratic_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ t : ℝ, ∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) < ⊤ := by
  have hton :
      (∫⁻ t : ℝ, ∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ ∂volume) =
      (∫⁻ z : ℝ, ∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂volume ∂μ) := by
    simpa only [zero_mul, mul_zero, neg_zero, Real.exp_zero, mul_one,
      neg_mul] using gaussian_double_tail_tonelli μ φ 0
  let g : ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-(φ * z))) *
      ENNReal.ofReal (z ^ 2 / 2)
  have hinner :
      (fun z : ℝ => ∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) *
          ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂volume) =
      (Ioi (0 : ℝ)).indicator g := by
    funext z
    by_cases hz : 0 < z
    · have hi := gaussian_double_tail_atom_full_lintegral φ z hz.le
      simpa [g, Set.indicator, hz] using hi
    · have hz0 : ∀ t : ℝ, ¬ (0 < t ∧ t < z) := by
        intro t h
        exact hz (lt_trans h.1 h.2)
      simp [g, Set.indicator, hz, hz0]
  have hbound :
      (∫⁻ z in Ioi (0 : ℝ), g z ∂μ) ≤
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂μ) := by
    have hmem : ∀ᵐ z : ℝ ∂μ.restrict (Ioi (0 : ℝ)),
        z ∈ Ioi (0 : ℝ) :=
      ae_restrict_mem (μ := μ) measurableSet_Ioi
    apply lintegral_mono_ae
    filter_upwards [hmem] with z hz
    have hle : z ^ 2 / 2 ≤ z ^ 2 := by
      nlinarith [sq_nonneg z]
    have hreal :
        Real.exp (-(φ * z)) * (z ^ 2 / 2) ≤
          Real.exp (-(φ * z)) * z ^ 2 :=
      mul_le_mul_of_nonneg_left hle (Real.exp_nonneg _)
    dsimp [g]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hfinite :=
    gaussian_esscher_damped_quadratic_integrable μ φ hφ hlevy
  rw [hton, hinner, lintegral_indicator measurableSet_Ioi]
  exact lt_of_le_of_lt hbound hfinite
