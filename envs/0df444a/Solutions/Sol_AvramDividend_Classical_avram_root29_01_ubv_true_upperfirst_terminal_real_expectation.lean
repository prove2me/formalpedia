-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_ubv_true_upperfirst_terminal_real_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T17:34:57.616659+00:00
-- url     : https://prove2.me/submissions/5bd7f123-4a1f-48d9-b7bf-7acc096aa650

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_true_horizon_completed_survival_integral_balance
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_stopped_horizon_components_le_scale_cap
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_rewards_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_uniform_nonnegative_bounded_integral_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal
/-- Original UBV upper-first stopped reward has expectation Wq(x). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (let F : Ω → ℝ := fun ω =>
      if twoSidedExitUpTime X (a-x) ω <
          twoSidedExitDownTime X (-x) ω then
        Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
      else 0;
    Integrable F P ∧ (∫ ω, F ω ∂P) = W x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S : ℕ → Ω → ℝ := fun n ω =>
    let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
    let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
    (if U < D ∧ U.toNNReal ≤ (n : ℝ≥0) then
      Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
    else 0) +
    (if ((n : ℝ≥0) : ℝ≥0∞) < U ∧ ((n : ℝ≥0) : ℝ≥0∞) < D then
      Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω)
    else 0)
  let F : Ω → ℝ := fun ω =>
    if twoSidedExitUpTime X (a-x) ω < twoSidedExitDownTime X (-x) ω then
      Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω)
    else 0
  have hBalance (n : ℕ) :
      Integrable (S n) P ∧ (∫ ω, S n ω ∂P) = W x :=
    avram_root29_01_ubv_true_horizon_completed_survival_integral_balance
      X hnbv q hq W hW a x ha hx0 hxa (n : ℝ≥0)
  have hNonneg (n : ℕ) (ω : Ω) : 0 ≤ S n ω := by
    obtain ⟨h1, h2⟩ := avram_ws01b_true_horizon_split_rewards_nonnegative
      X q W hW a x ha hx0 hxa (n : ℝ≥0) ω
    exact add_nonneg h1 h2
  have hCap (n : ℕ) (ω : Ω) : S n ω ≤ W a :=
    avram_ws01b_actual_stopped_horizon_components_le_scale_cap X q hq W hW a x ha hx0 hxa (n : ℝ≥0) ω
  have hConv : ∀ᵐ ω ∂P,
      Tendsto (fun n => S n ω) atTop (𝓝 (F ω)) :=
    Filter.Eventually.of_forall (fun ω =>
      avram_ws01b_true_horizon_split_reward_tendsto_upper_terminal X q hq W hW a x ha hx0 hxa ω)
  have hDct : Tendsto (fun n => ∫ ω, S n ω ∂P) atTop (𝓝 (∫ ω, F ω ∂P)) :=
    avram_ws01b_uniform_nonnegative_bounded_integral_transfer S F (W a)
      (hW.2.1 a (le_of_lt ha)) (fun n => (hBalance n).1) hNonneg hCap hConv
  have hKnown : Tendsto (fun n => ∫ ω, S n ω ∂P) atTop (𝓝 (W x)) := by
    have hEq : (fun n => ∫ ω, S n ω ∂P) = (fun _ : ℕ => W x) := funext (fun n => (hBalance n).2)
    rw [hEq]
    exact tendsto_const_nhds
  have hFm : AEStronglyMeasurable F P := aestronglyMeasurable_of_tendsto_ae
    atTop (fun n => (hBalance n).1.aestronglyMeasurable) hConv
  have hFn : ∀ᵐ ω ∂P, ‖F ω‖ ≤ ‖W a‖ := by
    filter_upwards [hConv] with ω hω
    have hNorm : ‖F ω‖ ≤ W a := by
      apply le_of_tendsto hω.norm
      exact Filter.Eventually.of_forall (fun n => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hNonneg n ω)]
          using hCap n ω)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (hW.2.1 a (le_of_lt ha))] using hNorm
  have hFInt : Integrable F P := (integrable_const (W a)).mono hFm hFn
  change Integrable F P ∧ (∫ ω, F ω ∂P) = W x
  exact ⟨hFInt, tendsto_nhds_unique hDct hKnown⟩
