-- Prove2me | solution 1 for AvramDividend.Classical.bv_scaled_deficit_laplace_tendsto_one_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:37:03.827924+00:00
-- url     : https://prove2.me/submissions/e8c41903-7bb3-4fb3-b48b-e22b701ae078

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Theorems.Thm_AvramDividend_Classical_bv_exponent_negative_jump_deficit_exact
import Theorems.Thm_AvramDividend_Classical_bv_inverse_frequency_mesh_gap_tendsto_zero
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (δ : ℕ → ℝ≥0) (θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθge : ∀ n, 1 ≤ θ n)
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c) :
    Tendsto (fun n : ℕ =>
      ∫ ω, Real.exp (θ n * X.X (δ n) ω) *
        Real.exp (-((δ n : ℝ) * X.drift * θ n)) ∂P)
      atTop (𝓝 (1 : ℝ)) := by
  have hr := bv_inverse_frequency_mesh_gap_tendsto_zero X hBV (fun n => (δ n : ℝ)) θ c hθ
    (fun n => by linarith [hθge n]) hProduct
  have h2 : Tendsto (fun n : ℕ => Real.exp (-((δ n : ℝ) * (X.drift * θ n - X.ψ (θ n))))) atTop (𝓝 1) := by
    have := (Real.continuous_exp.comp continuous_neg).tendsto 0
    simp only [Function.comp, neg_zero, Real.exp_zero] at this
    exact this.comp hr
  refine h2.congr fun n => ?_
  rw [bv_actual_levy_drift_normalised_laplace X hBV (δ n) (θ n) (hθge n),
    bv_exponent_negative_jump_deficit_exact X hBV (θ n) (hθge n)]
