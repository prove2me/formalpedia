-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.twist_set_double
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:39.203003+00:00
-- url     : https://prove2.me/submissions/89f75206-0193-43fb-9784-a85b7bdc0618

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : TwistSetDouble := by
  intro K _ _ _ J _ ε0 w h
  have hp : 0 ≤ 1 / (plc w : ℝ) ^ 2 := by positivity
  have e2 : (2 : ℝ) / (plc w : ℝ) ^ 2 = 1 / (plc w : ℝ) ^ 2 + 1 / (plc w : ℝ) ^ 2 := by ring
  rw [e2]
  by_cases hc : conjPl w = w
  · simp only [if_pos hc, add_zero] at h
    rw [hc, Finset.sum_add_distrib]
    linarith
  · simp only [if_neg hc] at h
    linarith
end Formalism.EigenvalueLevelCeiling
