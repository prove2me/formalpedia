-- Prove2me | solution 1 for DiscreteExpectation.rsIntegrable_identity_step
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:55:15.10736+00:00
-- url     : https://prove2.me/submissions/437be1c2-f70b-4d43-b86d-16a6132546b8

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F003
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F002
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
end
noncomputable section DiscreteExpectation
section DiscreteExpectation
open DiscreteExpectation

theorem solution {c a b : ℝ} (ha : a < c) (hb : c < b) :
    RSIntegrable (fun x => x) (stepIndicator c) a b :=
  ⟨rsIntegralWitness_identity_step ha hb⟩
end DiscreteExpectation
end DiscreteExpectation
