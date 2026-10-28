-- Prove2me | solution 3 for AvramDividend.Classical.bv_finite_activity_no_deficit_prefix_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:30:51.49605+00:00
-- url     : https://prove2.me/submissions/a92e3051-ae55-4fb0-b4d7-1beb97bc2bcc

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.MeasureTheory.Measure.MeasureSpace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The exponential zero atom is the probability of no drift deficit
    anywhere on the entire initial interval, for the actual process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
      X.drift * (s : ℝ) - X.X s ω = 0} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  let A : Set Ω := {ω | ∀ s : ℝ≥0, s ≤ t →
    X.drift * (s : ℝ) - X.X s ω = 0}
  let B : Set Ω := {ω | (t : ℝ) * X.drift - X.X t ω = 0}
  have hEq : A =ᵐ[P] B := by
    filter_upwards [bv_drift_deficit_ae_monotone_all_times X hBV] with ω hMono
    apply propext
    change (∀ s : ℝ≥0, s ≤ t →
      X.drift * (s : ℝ) - X.X s ω = 0) ↔
      (t : ℝ) * X.drift - X.X t ω = 0
    constructor
    · intro h
      simpa only [mul_comm] using h t le_rfl
    · intro hZero s hs
      have hlo : 0 ≤ X.drift * (s : ℝ) - X.X s ω := by
        have h := hMono (show (0 : ℝ≥0) ≤ s from zero_le)
        simpa [X.X_zero ω] using h
      have hhi : X.drift * (s : ℝ) - X.X s ω ≤ 0 := by
        have h := hMono hs
        simpa only [mul_comm, hZero] using h
      exact le_antisymm hhi hlo
  calc
    P.real A = P.real B := by
      exact congrArg ENNReal.toReal (measure_congr hEq)
    _ = Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) :=
      bv_actual_residual_zero_atom_survival X hBV hFinite t
