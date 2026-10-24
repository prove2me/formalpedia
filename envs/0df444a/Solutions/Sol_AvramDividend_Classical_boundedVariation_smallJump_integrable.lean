-- Prove2me | solution 1 for AvramDividend.Classical.boundedVariation_smallJump_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:50:29.360685+00:00
-- url     : https://prove2.me/submissions/3efec973-3b99-415d-956a-0cf3ff11448a

import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Finite variation makes the compensated small-negative-jump coordinate
    integrable with respect to the Lévy measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    IntegrableOn (fun y : ℝ => y) (Ioo (-1 : ℝ) 0) X.ν := by
  change Integrable (fun y : ℝ => y) (X.ν.restrict (Ioo (-1 : ℝ) 0))
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_def]
  simpa only [Real.enorm_eq_ofReal_abs] using hBV.2
