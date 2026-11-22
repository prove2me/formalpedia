-- Prove2me | solution 1 for AvramDividend.Classical.ftap_local_martingale_of_integrable_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:03:08.134815+00:00
-- url     : https://prove2.me/submissions/3e53a2de-5366-4972-a115-9b81bfaa69c5

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted from FTAPTheorem42/Stochastic/Martingale/Basic/DominatedLocalMartingale.lean
Original project: https://github.com/selpoG/lean-ftap-closedness
Source commit: 8c9c46e1b6e455f7d3069062957d4363879836ce
Released under Apache-2.0.
-/
import Mathlib
import Theorems.Thm_AvramDividend_Classical_ftap_dominated_martingale_limit
open Filter MeasureTheory Set
open scoped NNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [SigmaFiniteFiltration μ ℱ]
    {X : ℝ≥0 → Ω → ℝ}
    (hX : ProbabilityTheory.Locally
      (fun Y : ℝ≥0 → Ω → ℝ => Martingale Y ℱ μ) ℱ X μ)
    (hAdapted : StronglyAdapted ℱ X)
    (Z : Ω → ℝ) (hZ : Integrable Z μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ t, |X t ω| ≤ Z ω) :
    Martingale X ℱ μ := by
  let Y : ℕ → ℝ≥0 → Ω → ℝ := fun n =>
    MeasureTheory.stoppedProcess
      (fun t => {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω}.indicator (X t))
      (hX.localSeq n)
  have hYn : ∀ n, Martingale (Y n) ℱ μ := by
    intro n
    exact hX.stoppedProcess_localSeq n
  have hYlim : ∀ t, ∀ᵐ ω ∂μ,
      Tendsto (fun n => Y n t ω) atTop (𝓝 (X t ω)) := by
    intro t
    filter_upwards [hX.isLocalizingSequence_localSeq.tendsto_top] with ω hω
    have heq : ∀ᶠ n in atTop, Y n t ω = X t ω := by
      have hgt : ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < hX.localSeq n ω :=
        hω.eventually (Ioi_mem_nhds (WithTop.coe_lt_top t))
      filter_upwards [hgt] with n hn
      change MeasureTheory.stoppedProcess
        (fun t => {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω}.indicator (X t))
        (hX.localSeq n) t ω = X t ω
      rw [MeasureTheory.stoppedProcess_eq_of_le hn.le]
      have hnMem : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω} :=
        lt_of_le_of_lt bot_le hn
      exact Set.indicator_of_mem hnMem _
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) tendsto_const_nhds
  have hYdom : ∀ n t, ∀ᵐ ω ∂μ, ‖Y n t ω‖ ≤ Z ω := by
    intro n t
    filter_upwards [hdom] with ω hω
    have hZ0 : 0 ≤ Z ω := (abs_nonneg (X 0 ω)).trans (hω 0)
    change ‖MeasureTheory.stoppedProcess
      (fun t => {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω}.indicator (X t))
      (hX.localSeq n) t ω‖ ≤ Z ω
    rw [MeasureTheory.stoppedProcess_indicator_comm]
    by_cases hp : (⊥ : WithTop ℝ≥0) < hX.localSeq n ω
    · have hpMem : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω} := hp
      rw [Set.indicator_of_mem hpMem, Real.norm_eq_abs]
      exact hω _
    · have hpMem : ω ∉ {ω | (⊥ : WithTop ℝ≥0) < hX.localSeq n ω} := hp
      rw [Set.indicator_of_notMem hpMem, norm_zero]
      exact hZ0
  exact AvramDividend.Classical.ftap_dominated_martingale_limit
    X Y hAdapted hYn Z hZ hdom hYdom hYlim
