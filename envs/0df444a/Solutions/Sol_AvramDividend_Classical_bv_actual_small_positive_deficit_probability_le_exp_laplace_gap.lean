-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_small_positive_deficit_probability_le_exp_laplace_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:02:15.569326+00:00
-- url     : https://prove2.me/submissions/f38f6855-62e5-4df7-82f0-22f066de3eb7

import Theorems.Thm_AvramDividend_Classical_small_positive_deficit_measureReal_le_laplace_gap
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_deficit_laplace_nat
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual Lévy deficit Laplace law and its zero atom control a small positive deficit event. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) (a : ℝ)
    (D : Ω → ℝ)
    (hD : D = fun ω => (t : ℝ) * X.drift - X.X t ω)
    (hSmallMeas : MeasurableSet {ω : Ω | 0 < D ω ∧ (n : ℝ) * D ω ≤ a})
    (hZeroMeas : MeasurableSet {ω : Ω | D ω = 0})
    (hLeft : Integrable
      (fun ω => if 0 < D ω ∧ (n : ℝ) * D ω ≤ a then (1 : ℝ) else 0) P)
    (hRight : Integrable
      (fun ω => if D ω = 0 then (0 : ℝ) else Real.exp (-((n : ℝ) * D ω))) P)
    (hZero : Integrable
      (fun ω => if D ω = 0 then (1 : ℝ) else 0) P) :
    P.real {ω : Ω | 0 < D ω ∧ (n : ℝ) * D ω ≤ a} ≤
      Real.exp a *
        (Real.exp (-((t : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) -
          Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by
  subst D
  have hBound :=
    small_positive_deficit_measureReal_le_laplace_gap
      P (fun ω => (t : ℝ) * X.drift - X.X t ω)
      (n : ℝ) a hSmallMeas hZeroMeas hLeft hRight hZero
  have hLaplace :
      (∫ ω, Real.exp (-((n : ℝ) *
        ((t : ℝ) * X.drift - X.X t ω))) ∂P) =
      Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) := by
    simpa only [mul_neg] using
      (bv_actual_levy_drift_deficit_laplace_nat X hBV t n hn)
  have hAtom := bv_actual_residual_zero_atom_survival X hBV hFinite t
  rw [hLaplace, hAtom] at hBound
  exact hBound
