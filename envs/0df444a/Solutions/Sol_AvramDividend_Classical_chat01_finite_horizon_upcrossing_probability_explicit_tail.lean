-- Prove2me | solution 1 for AvramDividend.Classical.chat01_finite_horizon_upcrossing_probability_explicit_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:41:02.069931+00:00
-- url     : https://prove2.me/submissions/bfac24a5-e876-4d01-8e69-1569ac75c113

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_measurable_finite_horizon_upcrossing_probability_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Chernoff-form spatial tail bound removes the deterministic horizon
    discount from a measurable restricted first-upcrossing event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hAmeas : MeasurableSet A)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) :
    P A ≤ ENNReal.ofReal (Real.exp (q * t - φ * z)) := by
  have h :=
    chat01_measurable_finite_horizon_upcrossing_probability_bound
      X q hq φ hφ hroot z hz A hAmeas hA t htime
  have hcancel :
      ENNReal.ofReal (Real.exp (q * t)) *
        ENNReal.ofReal (Real.exp (-(q * t))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  have hcombine :
      ENNReal.ofReal (Real.exp (q * t)) *
        ENNReal.ofReal (Real.exp (-(φ * z))) =
          ENNReal.ofReal (Real.exp (q * t - φ * z)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp only [sub_eq_add_neg]
  calc
    P A = (ENNReal.ofReal (Real.exp (q * t)) *
        ENNReal.ofReal (Real.exp (-(q * t)))) * P A := by
          rw [hcancel, one_mul]
    _ = ENNReal.ofReal (Real.exp (q * t)) *
        (ENNReal.ofReal (Real.exp (-(q * t))) * P A) := by
          rw [mul_assoc]
    _ ≤ ENNReal.ofReal (Real.exp (q * t)) *
        ENNReal.ofReal (Real.exp (-(φ * z))) := by
          exact mul_le_mul_of_nonneg_left h (zero_le : 0 ≤ ENNReal.ofReal (Real.exp (q * t)))
    _ = _ := hcombine
