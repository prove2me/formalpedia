-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed13_original_finite_activity_nu_smallstrip_real_integral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:00:42.737363+00:00
-- url     : https://prove2.me/submissions/a491926c-16e1-47bd-95f2-d8d29717dbc9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed13_original_finite_activity_nu_smallstrip_lintegral_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- The real compensator in the finite-activity source is bounded by
the strip width times the total negative jump intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (ε : ℝ) (hε : 0 ≤ ε)
    (S : Set ℝ) (hS : MeasurableSet S) (hSub : S ⊆ Ioo (-ε) 0) :
    |∫ z in S, z ∂X.ν| ≤
      ε * (X.ν (Iio (0 : ℝ))).toReal := by
  have hmass : ENNReal.ofReal ε * X.ν (Iio (0 : ℝ)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hFinite
  have hNorm :
      |∫ z in S, z ∂X.ν| ≤
        (∫⁻ z in S, ENNReal.ofReal |z| ∂X.ν).toReal := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_lintegral_norm
        (μ := X.ν.restrict S) (fun z : ℝ => z))
  have hSmall :
      (∫⁻ z in S, ENNReal.ofReal |z| ∂X.ν) ≤
      ENNReal.ofReal ε * X.ν (Iio (0 : ℝ)) := by
    exact (lintegral_mono_set hSub).trans
      (avram_ubv_mixed13_original_finite_activity_nu_smallstrip_lintegral_le
        X hFinite ε hε)
  calc
    |∫ z in S, z ∂X.ν| ≤
        (∫⁻ z in S, ENNReal.ofReal |z| ∂X.ν).toReal := hNorm
    _ ≤ (ENNReal.ofReal ε * X.ν (Iio (0 : ℝ))).toReal :=
      ENNReal.toReal_mono hmass hSmall
    _ = ε * (X.ν (Iio (0 : ℝ))).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε]
