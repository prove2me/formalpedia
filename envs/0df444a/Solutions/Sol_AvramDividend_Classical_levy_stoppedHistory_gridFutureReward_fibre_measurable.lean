-- Prove2me | solution 1 for AvramDividend.Classical.levy_stoppedHistory_gridFutureReward_fibre_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T12:16:50.027964+00:00
-- url     : https://prove2.me/submissions/b7f9f1ca-274a-4964-809c-f193807ce77e

import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_stoppedEvent_upperGridFibre_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The whole-path future reward on an adapted stopped-time fibre is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hfibres : ∀ n s,
      MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s})
    (n : ℕ) (s : ℝ≥0)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Measurable g) :
    Measurable
      (Set.indicator (A ∩ {ω : Ω | τn n ω = s})
        (fun ω => g (fun t : ℝ≥0 =>
          X.X (s + t) ω - X.X s ω))) := by
  have hpath : Measurable (fun ω : Ω => fun t : ℝ≥0 =>
      X.X (s + t) ω - X.X s ω) := by
    apply measurable_pi_iff.mpr
    intro t
    exact ((X.adapted (s + t)).mono (𝓕.le (s + t)) le_rfl).sub
      ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hevent : MeasurableSet
      (A ∩ {ω : Ω | τn n ω = s}) :=
    (𝓕.le s (A ∩ {ω : Ω | τn n ω = s}))
      (stoppedEvent_upperGridFibre_measurable
        τ A hA τn habove hfibres n s)
  exact (hg.comp hpath).indicator hevent