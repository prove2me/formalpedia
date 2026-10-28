-- Prove2me | solution 1 for AvramDividend.Classical.levy_finiteStopping_boundedReward_scalar_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:47:22.625523+00:00
-- url     : https://prove2.me/submissions/8d4cc7fb-396b-4b08-8045-f457d2593c2b

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_continuousMeasurableReward_scalar_markov
import Theorems.Thm_AvramDividend_Classical_levy_futurePath_boundedReward_lintegral_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strong Markov at a finite stopping time without a separate reward-finiteness hypothesis. -/
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
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')))) :
    (∫⁻ ω, Set.indicator A
      (fun ω' : Ω => g (fun t : ℝ≥0 =>
        X.X (τ ω' + t) ω' - X.X (τ ω') ω')) ω ∂P) =
    P A * (∫⁻ y, g y ∂(Measure.map
      (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P)) := by
  have hRewardFinite :=
    levy_futurePath_boundedReward_lintegral_finite X g C hbound hfin
  exact levy_finiteStopping_continuousMeasurableReward_scalar_markov
    X τ hstop A hA g hg hgm C hbound hfin hMeas hRewardFinite
