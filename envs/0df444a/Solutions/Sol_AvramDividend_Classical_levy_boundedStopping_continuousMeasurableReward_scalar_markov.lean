-- Prove2me | solution 1 for AvramDividend.Classical.levy_boundedStopping_continuousMeasurableReward_scalar_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:12:05.429711+00:00
-- url     : https://prove2.me/submissions/de6b7322-78d0-40b2-b841-2705a6f27fe5

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_ennrealFutureReward_limit
import Theorems.Thm_AvramDividend_Classical_levy_upperGrid_stoppedHistory_scalar_markov
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_gridFutureReward_measurable
import Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_reward_tendsto_of_bounded
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

/-- Bounded-time strong Markov for bounded continuous whole-path Lévy rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  obtain ⟨τn, grid, hgrid, hfibres, habove, hτlim, hglim⟩ :=
    levy_boundedStopping_grid_ennrealFutureReward_limit
      X τ hstop T hτT g hg
  have hfibresAll : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s} := by
    intro n s
    by_cases hs : s ∈ grid n
    · exact hfibres n s hs
    · have hempty : {ω : Ω | τn n ω = s} = ∅ := by
        ext ω
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        intro heq
        exact hs (heq ▸ hgrid n ω)
      simpa [hempty] using
        (MeasurableSet.empty : MeasurableSet[𝓕 s] (∅ : Set Ω))
  have hAm : MeasurableSet A :=
    stoppedHistory_event_measurable τ A hA
  let v : ℝ≥0∞ := P A * (∫⁻ y, g y ∂(Measure.map
    (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P))
  have hscalar (n : ℕ) :
      (∫⁻ ω, Set.indicator A
        (fun ω' : Ω => g (fun t : ℝ≥0 =>
          X.X (τn n ω' + t) ω' - X.X (τn n ω') ω')) ω ∂P) = v :=
    levy_upperGrid_stoppedHistory_scalar_markov
      X τ A hA hAm τn habove hfibresAll
      n (grid n) (hgrid n) g hgm
  have hmeas (n : ℕ) : Measurable (Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τn n ω' + t) ω' - X.X (τn n ω') ω'))) :=
    levy_stoppedHistory_gridFutureReward_measurable
      X τ A hA τn habove hfibresAll
      n (grid n) (hgrid n) g hgm
  have hDCT := lintegral_stoppedEvent_reward_tendsto_of_bounded
    P A
    (fun n ω => g (fun t : ℝ≥0 =>
      X.X (τn n ω + t) ω - X.X (τn n ω) ω))
    (fun ω => g (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω))
    hmeas hglim C (fun n ω => hbound _) hfin
  have hconstant :
      (fun n : ℕ => ∫⁻ ω, Set.indicator A
        (fun ω' : Ω => g (fun t : ℝ≥0 =>
          X.X (τn n ω' + t) ω' - X.X (τn n ω') ω')) ω ∂P) =
      (fun _ : ℕ => v) := by
    funext n
    exact hscalar n
  rw [hconstant] at hDCT
  exact tendsto_nhds_unique hDCT tendsto_const_nhds
