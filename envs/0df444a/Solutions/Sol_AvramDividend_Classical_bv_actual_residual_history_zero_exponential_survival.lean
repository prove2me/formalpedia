-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_residual_history_zero_exponential_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:58:18.754413+00:00
-- url     : https://prove2.me/submissions/e1787a03-6351-4512-a960-f37ab1d1c7ce

import Theorems.Thm_AvramDividend_Classical_monotone_zero_horizon_iff_history_zero
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.MeasureTheory.Measure.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Genuine no-residual-through-horizon survival has the exact finite-jump exponential law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
      (s : ℝ) * X.drift - X.X s ω = 0} =
        Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  have hEq :
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
        (s : ℝ) * X.drift - X.X s ω = 0} =ᵐ[P]
      {ω : Ω | (t : ℝ) * X.drift - X.X t ω = 0} := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hw
    change (∀ s : ℝ≥0, s ≤ t →
        (s : ℝ) * X.drift - X.X s ω = 0) =
        ((t : ℝ) * X.drift - X.X t ω = 0)
    apply propext
    have h0 : ((0 : ℝ≥0) : ℝ) * X.drift - X.X 0 ω = 0 := by
      simp [X.X_zero]
    exact (monotone_zero_horizon_iff_history_zero
      (fun s : ℝ≥0 => (s : ℝ) * X.drift - X.X s ω) hw h0 t).symm
  exact (measureReal_congr hEq).trans
    (bv_actual_residual_zero_atom_survival X hBV hFinite t)
