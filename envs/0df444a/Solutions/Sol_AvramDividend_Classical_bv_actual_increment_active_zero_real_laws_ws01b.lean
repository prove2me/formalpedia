-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_increment_active_zero_real_laws_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:11:32.237682+00:00
-- url     : https://prove2.me/submissions/09ee1310-0c0f-4271-a059-a791d6844825

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_positive_probability
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_increment_zero_probability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Active and inactive Lévy residual cells have exact exponential masses. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P.real {ω : Ω | X.X t ω - X.X s ω <
      X.drift * (((t - s : ℝ≥0) : ℝ))} =
        1 - Real.exp (-(((t - s : ℝ≥0) : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal)) ∧
    P.real {ω : Ω | X.X t ω - X.X s ω =
      X.drift * (((t - s : ℝ≥0) : ℝ))} =
        Real.exp (-(((t - s : ℝ≥0) : ℝ) *
          (X.ν (Iio (0 : ℝ))).toReal)) := by
  have hD (ω : Ω) :
      ((t : ℝ) * X.drift - X.X t ω) -
        ((s : ℝ) * X.drift - X.X s ω) =
      ((t - s : ℝ≥0) : ℝ) * X.drift -
        (X.X t ω - X.X s ω) := by
    rw [NNReal.coe_sub hst]
    ring
  have hActive :
      {ω : Ω | X.X t ω - X.X s ω < X.drift * (((t - s : ℝ≥0) : ℝ))} =
      {ω : Ω | 0 <
        ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hD ω]
    constructor <;> intro h <;> linarith
  have hZero :
      {ω : Ω | X.X t ω - X.X s ω = X.drift * (((t - s : ℝ≥0) : ℝ))} =
      {ω : Ω |
        ((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hD ω]
    constructor <;> intro h <;> linarith
  constructor
  · rw [hActive]
    exact bv_actual_residual_increment_positive_probability X hBV hFinite s t hst
  · rw [hZero]
    exact bv_actual_residual_increment_zero_probability X hBV hFinite s t hst
