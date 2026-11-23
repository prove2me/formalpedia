-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.eig_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:38.537986+00:00
-- url     : https://prove2.me/submissions/505c30f0-3b6d-4bf0-a6f7-43eff9ee6271

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
variable (K : Type) [Field K] [NumberField K] [StarRing K]
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : eig (1 : Representation K Unit K) ⊤ (fun _ => (1 : 𝓞 K)) = ⊤ := by
  apply eq_top_iff.2
  intro x _
  unfold eig
  rw [Submodule.mem_iInf]
  intro u
  rw [LinearMap.mem_ker]
  simp
end Formalism.EigenvalueLevelCeiling
