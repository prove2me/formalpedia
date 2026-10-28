-- Prove2me | solution 1 for AvramDividend.Classical.bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:27:26.077005+00:00
-- url     : https://prove2.me/submissions/cad0e096-379b-4a4c-aaa0-4f6d06784d9f

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_laplace_large_deficit_probability_tendsto_zero_ae_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_scaled_deficit_laplace_tendsto_one_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
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
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω |
        a ≤ θ n * ((δ n : ℝ) * X.drift - X.X (δ n) ω)})
      atTop (𝓝 (0 : ℝ)) := by
  haveI := X.isProbability
  set D : ℕ → Ω → ℝ := fun n ω => θ n * ((δ n : ℝ) * X.drift - X.X (δ n) ω) with hDdef
  have hXm : ∀ n, Measurable (X.X (δ n)) := fun n => (X.adapted (δ n)).mono (𝓕.le (δ n)) le_rfl
  have hDm : ∀ n, Measurable (D n) := fun n =>
    measurable_const.mul (measurable_const.sub (hXm n))
  have hDnn : ∀ n, ∀ᵐ ω ∂P, 0 ≤ D n ω := by
    intro n
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV (δ n)] with ω hω
    exact mul_nonneg (by linarith [hθge n]) (by linarith)
  have hMeas : ∀ n, MeasurableSet {ω : Ω | a ≤ D n ω} := fun n =>
    measurableSet_le measurable_const (hDm n)
  have hExp : ∀ n, Integrable (fun ω => Real.exp (-D n ω)) P := by
    intro n
    refine Integrable.of_bound (Real.measurable_exp.comp (hDm n).neg).aestronglyMeasurable 1 ?_
    filter_upwards [hDnn n] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (by linarith)
  have hLeft : ∀ n, Integrable
      (fun ω => if a ≤ D n ω then (1 - Real.exp (-a) : ℝ) else 0) P := by
    intro n
    refine Integrable.of_bound ?_ |1 - Real.exp (-a)| (Filter.Eventually.of_forall fun ω => ?_)
    · exact (Measurable.ite (hMeas n) measurable_const measurable_const).aestronglyMeasurable
    · split_ifs <;> simp
  have hL := bv_scaled_deficit_laplace_tendsto_one_ws01b X hBV δ θ c hθ hθge hProduct
  have hL' : Tendsto (fun n : ℕ => ∫ ω, Real.exp (-D n ω) ∂P) atTop (𝓝 (P.real Set.univ)) := by
    rw [probReal_univ]
    refine hL.congr fun n => integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hDdef]
    rw [← Real.exp_add]; congr 1; ring
  exact laplace_large_deficit_probability_tendsto_zero_ae_ws01b P D a ha hDnn hMeas hLeft
    (integrable_const 1) hExp hL'
