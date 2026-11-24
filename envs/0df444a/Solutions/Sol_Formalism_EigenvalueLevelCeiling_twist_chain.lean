-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.twist_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:56:16.716801+00:00
-- url     : https://prove2.me/submissions/1f5d676c-c825-4200-8bb9-71d23ea291b4

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxMono


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
theorem _root_.solution : TwChain := by
  intro K _ _ _ Z _ _ _ _ _ w W e A Th0 ThJ X₃ hA h0 hJ hle ε h
  have a := idxMono K Z w W A _ _ hA h0 hJ (Submodule.map_mono hle)
  have a' : (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) := by exact_mod_cast a
  linarith
end Formalism.EigenvalueLevelCeiling
