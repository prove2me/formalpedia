-- Prove2me | solution 1 for AvramDividend.Classical.bv_infinite_activity_residual_laplace_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:06:06.163118+00:00
-- url     : https://prove2.me/submissions/96b3f98f-498f-4aea-b7c8-33fcf9e5c925

import Theorems.Thm_AvramDividend_Classical_bv_exponent_drift_deficit_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Infinite activity makes positive-time drift-residual Laplace moments vanish. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (t : ℝ≥0) (ht : 0 < t) :
    Tendsto
      (fun n : ℕ =>
        ∫ ω, Real.exp ((n : ℝ) * (X.X t ω - (t : ℝ) * X.drift)) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hgap := bv_exponent_drift_deficit_tendsto_atTop X hBV hνinf
  have htreal : 0 < (t : ℝ) := by exact_mod_cast ht
  have harg0 : Tendsto
      (fun n : ℕ =>
        (X.drift * (n : ℝ) - X.ψ (n : ℝ)) * (-(t : ℝ)))
      atTop atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg (neg_lt_zero.mpr htreal) hgap
  have harg : Tendsto
      (fun n : ℕ => -((t : ℝ) *
        (X.drift * (n : ℝ) - X.ψ (n : ℝ))))
      atTop atBot := by
    convert harg0 using 1
    ext n
    ring
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (-((t : ℝ) *
        (X.drift * (n : ℝ) - X.ψ (n : ℝ)))))
      atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp harg
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
