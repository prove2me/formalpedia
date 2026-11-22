-- Prove2me | solution 1 for AvramDividend.Classical.ftap_dominated_martingale_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:59:06.95892+00:00
-- url     : https://prove2.me/submissions/4f726cd2-245e-4931-bd5a-666dd8c90faf

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from DominatedLocalMartingale.lean, FTAPTheorem42 (Apache-2.0).
Source commit: 8c9c46e1b6e455f7d3069062957d4363879836ce.
-/
import Mathlib
open Filter MeasureTheory Set
open scoped NNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
    (X : ℝ≥0 → Ω → ℝ)
    (Y : ℕ → ℝ≥0 → Ω → ℝ)
    (hAdapted : StronglyAdapted ℱ X)
    (hYn : ∀ n, Martingale (Y n) ℱ μ)
    (Z : Ω → ℝ) (hZ : Integrable Z μ)
    (hdomX : ∀ᵐ ω ∂μ, ∀ t, |X t ω| ≤ Z ω)
    (hYdom : ∀ n t, ∀ᵐ ω ∂μ, ‖Y n t ω‖ ≤ Z ω)
    (hYlim : ∀ t, ∀ᵐ ω ∂μ,
      Tendsto (fun n => Y n t ω) atTop (𝓝 (X t ω))) :
    Martingale X ℱ μ := by
  have hXIntegrable : ∀ t, Integrable (X t) μ := by
    intro t
    apply hZ.mono' hAdapted.stronglyMeasurable.aestronglyMeasurable
    filter_upwards [hdomX] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  refine ⟨hAdapted, ?_⟩
  intro i j hij
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le i) (hXIntegrable j)
  · intro s hs hμs
    exact (hXIntegrable i).integrableOn
  · intro s hs hμs
    have hs0 : MeasurableSet s := ℱ.le i s hs
    let H : ℝ≥0 → ℕ → Ω → ℝ := fun t n => s.indicator (Y n t)
    have hHMeas (t : ℝ≥0) : ∀ n, AEStronglyMeasurable (H t n) μ := by
      intro n
      exact ((hYn n).stronglyMeasurable t).mono
        (ℱ.le t) |>.indicator hs0 |>.aestronglyMeasurable
    have hHBound (t : ℝ≥0) : ∀ n, ∀ᵐ ω ∂μ, ‖H t n ω‖ ≤ Z ω := by
      intro n
      filter_upwards [hYdom n t, hdomX] with ω hloc hω
      by_cases hωs : ω ∈ s
      · simpa [H, Set.indicator_of_mem hωs] using hloc
      · simp [H, Set.indicator_of_notMem hωs,
          (abs_nonneg (X 0 ω)).trans (hω 0)]
    have hHLim (t : ℝ≥0) : ∀ᵐ ω ∂μ, Tendsto (fun n => H t n ω)
        atTop (𝓝 (s.indicator (X t) ω)) := by
      filter_upwards [hYlim t] with ω hω
      by_cases hωs : ω ∈ s
      · simpa [H, Set.indicator_of_mem hωs] using hω
      · simp [H, Set.indicator_of_notMem hωs]
    have hHInt (t : ℝ≥0) :
        Tendsto (fun n => ∫ ω, H t n ω ∂μ) atTop
          (𝓝 (∫ ω, s.indicator (X t) ω ∂μ)) :=
      tendsto_integral_of_dominated_convergence Z
        (hHMeas t) hZ (hHBound t) (hHLim t)
    have hEq : ∀ n, (∫ ω, H i n ω ∂μ) = ∫ ω, H j n ω ∂μ := by
      intro n
      simpa only [H, integral_indicator hs0] using
        (hYn n).setIntegral_eq hij hs
    have hLimits := tendsto_nhds_unique (hHInt i)
      ((hHInt j).congr' (Eventually.of_forall fun n => (hEq n).symm))
    simpa only [integral_indicator hs0] using hLimits
  · exact (hAdapted i).aestronglyMeasurable
