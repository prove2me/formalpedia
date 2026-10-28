-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_continuousMeasurableReward_scalar_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:38:03.443423+00:00
-- url     : https://prove2.me/submissions/faadec8e-3e09-492a-aa6a-e6f40b25180b

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_stoppedHistory_truncated_scalar_markov
import Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_horizon_tendsto
import Theorems.Thm_AvramDividend_Classical_stoppedHistory_event_probability_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- General finite-time strong Markov for continuous measurable bounded future-path rewards. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hg : Continuous g) (hgm : Measurable g)
    (C : ℝ≥0∞) (hbound : ∀ y, g y ≤ C)
    (hfin : (∫⁻ _ : Ω, C ∂P) ≠ ∞)
    (hMeas : ∀ n : ℕ, Measurable (Set.indicator
      (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)})
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω'))))
    (hRewardFinite : (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) ≠ ∞) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  let f : Ω → ℝ≥0∞ :=
    fun ω => g (fun t : ℝ≥0 =>
      X.X (τ ω + t) ω - X.X (τ ω) ω)
  let c : ℝ≥0∞ := ∫⁻ y, g y ∂(Measure.map
    (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)
  have hreward :
      Tendsto (fun n : ℕ =>
        ∫⁻ ω, Set.indicator
          (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) f ω ∂P)
        atTop (nhds (∫⁻ ω, Set.indicator A f ω ∂P)) :=
    lintegral_stoppedEvent_horizon_tendsto
      P τ A f hMeas C (fun ω => hbound _) hfin
  have hprob :
      Tendsto (fun n : ℕ =>
        P (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}))
      atTop (nhds (P A)) :=
    stoppedHistory_event_probability_tendsto P τ A
  have hmul :
      Tendsto (fun n : ℕ =>
        P (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) * c)
        atTop (nhds (P A * c)) := by
    exact ENNReal.Tendsto.mul_const hprob (Or.inr hRewardFinite)
  have htrunc (n : ℕ) :
      (∫⁻ ω, Set.indicator
        (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) f ω ∂P) =
      P (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) * c := by
    exact levy_stoppedHistory_truncated_scalar_markov
      X τ hstop A hA (n : ℝ≥0) g hg hgm C hbound hfin
  have heq :
      (fun n : ℕ => ∫⁻ ω, Set.indicator
        (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) f ω ∂P) =
      (fun n : ℕ =>
        P (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) * c) := by
    funext n
    exact htrunc n
  rw [heq] at hreward
  change (∫⁻ ω, Set.indicator A f ω ∂P) = P A * c
  exact tendsto_nhds_unique hreward hmul
