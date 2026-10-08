-- Prove2me | solution 1 for AvramDividend.Classical.esscher_negative_jumps_levy_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:23:08.345683+00:00
-- url     : https://prove2.me/submissions/857bf56a-b468-4350-b1de-dc68bd495a5e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- A nonnegative Esscher exponent reduces the negative-jump density
pointwise; therefore it preserves the Lévy integrability bound. -/
theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hneg : ν (Ici 0) = 0)
    (hlevy : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
      ∂(ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) < ⊤ := by
  have hneg_ae : ∀ᵐ y : ℝ ∂ν, y < 0 := by
    apply (ae_iff).2
    have hset : {y : ℝ | ¬ y < 0} = Ici (0 : ℝ) := by
      ext y
      simp
    rw [hset]
    exact hneg
  have hf :
      Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))) := by
    fun_prop
  have hg :
      Measurable (fun y : ℝ => ENNReal.ofReal (min 1 (y ^ 2))) := by
    fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul ν hf hg]
  apply lt_of_le_of_lt ?_ hlevy
  apply lintegral_mono_ae
  filter_upwards [hneg_ae] with y hy
  have hφy : φ * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hφ (le_of_lt hy)
  have hexp : Real.exp (φ * y) ≤ 1 :=
    (Real.exp_le_one_iff).2 hφy
  have hf_le : ENNReal.ofReal (Real.exp (φ * y)) ≤ 1 :=
    ENNReal.ofReal_le_one.mpr hexp
  calc
    ENNReal.ofReal (Real.exp (φ * y)) *
        ENNReal.ofReal (min 1 (y ^ 2)) ≤
        1 * ENNReal.ofReal (min 1 (y ^ 2)) :=
      mul_le_mul_of_nonneg_right hf_le (zero_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal (min 1 (y ^ 2)))
    _ = ENNReal.ofReal (min 1 (y ^ 2)) := one_mul _
