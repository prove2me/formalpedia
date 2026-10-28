-- Prove2me | solution 1 for AvramDividend.Classical.canonical_drifted_brownian_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:41:00.790157+00:00
-- url     : https://prove2.me/submissions/c894d7aa-3320-463d-a5e0-894b54e47bc1

import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
import Mathlib.Probability.Process.Filtration

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory
open scoped NNReal

theorem solution
    (t : ℝ≥0) :
    Measurable (fun ω : ℝ≥0 → ℝ =>
      ProbabilityTheory.brownian t ω - ProbabilityTheory.brownian 0 ω - (t : ℝ)) := by
  have ht : Measurable (ProbabilityTheory.brownian t) :=
    ProbabilityTheory.isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec.1 t
  have hz : Measurable (ProbabilityTheory.brownian 0) :=
    ProbabilityTheory.isPreBrownianReal_preBrownian.exists_continuous_modification.choose_spec.1 0
  exact (ht.sub hz).sub measurable_const
