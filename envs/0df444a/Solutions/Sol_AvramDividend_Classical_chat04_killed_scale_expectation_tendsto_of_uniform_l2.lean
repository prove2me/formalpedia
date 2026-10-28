-- Prove2me | solution 1 for AvramDividend.Classical.chat04_killed_scale_expectation_tendsto_of_uniform_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:43:00.797959+00:00
-- url     : https://prove2.me/submissions/b055ad7b-3ccf-4c20-a7b1-99dec4c9916a

import Theorems.Thm_AvramDividend_Classical_chat04_killed_scale_payoff_measurable_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_killed_deterministic_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat04_levy_closed_killed_discounted_scale_rightCont
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

/-- Uniform second moments turn pathwise killed q-scale right-continuity
    into convergence of killed expectations along right-hand sequences. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N t₀ : ℝ≥0) (t : ℕ → ℝ≥0)
    (htN : ∀ n, t n ≤ N)
    (htend : Tendsto t atTop (𝓝[Ici t₀] t₀)) :
    Tendsto
      (fun n => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t n : ℝ))) *
            W (x + X.X (t n) u)) ω ∂P)
      atTop
      (𝓝 (∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t₀ → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t₀ : ℝ))) *
            W (x + X.X t₀ u)) ω ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let S (u : ℝ≥0) : Set Ω :=
    {ω | ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω}
  let F (u : ℝ≥0) (ω : Ω) :=
    Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)
  let Y (n : ℕ) : Ω → ℝ := (S (t n)).indicator (F (t n))
  let Z : Ω → ℝ := (S t₀).indicator (F t₀)
  have hbase (u : ℝ≥0) :
      Measurable ((S u).indicator (F u)) ∧
      (∀ ω, 0 ≤ (S u).indicator (F u) ω) := by
    simpa only [S, F] using
      (chat04_killed_scale_payoff_measurable_nonnegative X q W hW x u)
  have hYm : ∀ n, AEStronglyMeasurable (Y n) P :=
    fun n => (hbase (t n)).1.aestronglyMeasurable
  have hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω :=
    fun n => Filter.Eventually.of_forall (hbase (t n)).2
  have hZm : AEStronglyMeasurable Z P :=
    (hbase t₀).1.aestronglyMeasurable
  have hdisc : Continuous (fun u : ℝ≥0 =>
      Real.exp (-(q * (u : ℝ)))) := by fun_prop
  have hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)) := by
    apply Filter.Eventually.of_forall
    intro ω
    classical
    have hc := (chat04_levy_closed_killed_discounted_scale_rightCont
      X q x W hW hzero _ hdisc ω t₀).tendsto.comp htend
    have hpoint (u : ℝ≥0) :
        (S u).indicator (F u) ω =
          (if (∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω) then F u ω else 0) := by
      by_cases hs : ω ∈ S u
      · have hsurv : ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω := hs
        simp only [Set.indicator_of_mem hs, if_pos hsurv]
      · have hsurv : ¬ ∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω := hs
        simp only [Set.indicator_of_notMem hs, if_neg hsurv]
    change Tendsto (fun n => (S (t n)).indicator (F (t n)) ω)
      atTop (𝓝 ((S t₀).indicator (F t₀) ω))
    simp_rw [hpoint]
    simpa only [F, Function.comp_def] using hc
  let C : ℝ := ((X.ψ θ - q)⁻¹)^2 *
    Real.exp (2 * θ * (x + 1) + (N : ℝ) * max (X.ψ (2 * θ)) 0)
  have hC : 0 ≤ C :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  have hY2 : ∀ n, Integrable (fun ω => (Y n ω)^2) P ∧
      ∫ ω, (Y n ω)^2 ∂P ≤ C := by
    intro n
    have hS : MeasurableSet (S (t n)) :=
      chat04_shifted_lower_survival_measurable_no_schedule X x (t n)
    simpa [Y, F, S, C] using
      (chat04_killed_deterministic_horizon_scale_l2_bound
        X q hq W hW θ x hθ hψ N (t n) (htN n)
        (S (t n)) hS)
  exact (nonnegative_integral_tendsto_of_uniform_second_moment
    Y Z hYm hY0 hZm hconv C hC hY2).2
