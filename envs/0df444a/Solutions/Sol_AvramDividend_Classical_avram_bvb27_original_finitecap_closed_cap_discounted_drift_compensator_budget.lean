-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb27_original_finitecap_closed_cap_discounted_drift_compensator_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:02:16.883538+00:00
-- url     : https://prove2.me/submissions/31570414-dccd-4101-90cd-53d45ff1bae9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite_activity_closed_cap_generator_HJB
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hq : 0 < q) (T : ℝ) (hT : 0 ≤ T) :
    X.drift * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) +
      Real.exp ((-q) * T) * w C.toReal ≤
    w C.toReal -
      (∫ z in Iio (0 : ℝ), w (C.toReal + z) - w C.toReal ∂X.ν) *
        (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t))  := by
  let I : ℝ := ∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)
  let K : ℝ := ∫ z in Iio (0 : ℝ),
    w (C.toReal + z) - w C.toReal ∂X.ν
  have hSign : X.drift + K - q * w C.toReal ≤ 0 := by
    exact avram_bv_finite_activity_closed_cap_generator_HJB
      X hStanding hBV hActivity q w C hC hFinite
      hwCont hwNeg hwGen hwGrad
  have hIntegral :
      q * I + Real.exp ((-q) * T) = 1 :=
    avram_bvb23_original_discounted_zero_contact_budget_identity q T hq hT
  have hExp : Real.exp ((-q) * T) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith [mul_nonneg hq.le hT]
  have hINonneg : 0 ≤ I := by
    nlinarith
  have hProduct : (X.drift + K - q * w C.toReal) * I ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hSign hINonneg
  have hExpEq : Real.exp ((-q) * T) = 1 - q * I := by
    linarith [hIntegral]
  change X.drift * I + Real.exp ((-q) * T) * w C.toReal ≤
    w C.toReal - K * I
  calc
    X.drift * I + Real.exp ((-q) * T) * w C.toReal =
        (X.drift + K - q * w C.toReal) * I +
          w C.toReal - K * I := by
            rw [hExpEq]
            ring
    _ ≤ w C.toReal - K * I := by linarith [hProduct]
