-- Prove2me | solution 2 for AvramDividend.Classical.canonical_drifted_brownian_natural_adapted
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:45:37.399923+00:00
-- url     : https://prove2.me/submissions/97b312d5-7dc5-442a-bfac-6492f35d87f6

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Mathlib.Probability.Process.Adapted
import Mathlib.Tactic

open ProbabilityTheory MeasureTheory
open scoped NNReal
theorem solution :
    let X : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t ω =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)
    ∃ hmeas : ∀ t : ℝ≥0, StronglyMeasurable (X t),
      Adapted (Filtration.natural X hmeas) X := by
  intro X
  have hb : ∀ t, Measurable (ProbabilityTheory.brownian t) :=
    isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec.1
  have hm : ∀ t, Measurable (X t) := fun t => ((hb t).sub (hb 0)).sub_const _
  refine ⟨fun t => (hm t).stronglyMeasurable, fun i => ?_⟩
  exact ((Filtration.stronglyAdapted_natural (fun t => (hm t).stronglyMeasurable)) i).measurable
