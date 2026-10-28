-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_residual_laplace_tendsto_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:30:43.441955+00:00
-- url     : https://prove2.me/submissions/291c1b9f-06a9-4d4c-b99a-158be76c26c3

import Theorems.Thm_AvramDividend_Classical_bv_actual_drift_exponent_gap_tendsto_intensity
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- At a fixed time, the actual residual's negative Laplace moments converge to Poisson survival. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, Real.exp ((n : ℝ) * (X.X t ω - (t : ℝ) * X.drift)) ∂P)
      atTop (𝓝 (Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)))) := by
  have hgap := bv_actual_drift_exponent_gap_tendsto_intensity X hBV hFinite
  have harg : Tendsto
      (fun n : ℕ => -((t : ℝ) *
        (X.drift * (n : ℝ) - X.ψ (n : ℝ))))
      atTop (𝓝 (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) :=
    (hgap.const_mul (t : ℝ)).neg
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (-((t : ℝ) *
        (X.drift * (n : ℝ) - X.ψ (n : ℝ)))))
      atTop (𝓝 (Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)))) :=
    (Real.continuous_exp.tendsto _).comp harg
  have heq : (fun n : ℕ =>
        ∫ ω, Real.exp ((n : ℝ) * (X.X t ω - (t : ℝ) * X.drift)) ∂P) =ᶠ[atTop]
      (fun n : ℕ => Real.exp (-((t : ℝ) *
        (X.drift * (n : ℝ) - X.ψ (n : ℝ))))) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc
      (∫ ω, Real.exp ((n : ℝ) * (X.X t ω - (t : ℝ) * X.drift)) ∂P) =
        (∫ ω, Real.exp ((n : ℝ) * X.X t ω) *
          Real.exp (-((t : ℝ) * X.drift * (n : ℝ))) ∂P) := by
            congr 1
            funext ω
            rw [← Real.exp_add]
            congr 1
            ring
      _ = Real.exp (-((t : ℝ) *
          ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) :=
          bv_actual_levy_drift_normalised_laplace X hBV t (n : ℝ) hn1
      _ = Real.exp (-((t : ℝ) *
          (X.drift * (n : ℝ) - X.ψ (n : ℝ)))) := by
            rw [bv_exponent_negative_jump_deficit_exact X hBV (n : ℝ) hn1]
  exact hexp.congr' heq.symm
