-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.map_id_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:38.880153+00:00
-- url     : https://prove2.me/submissions/4c876653-bb33-43c6-b727-0b51109d254a

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
theorem _root_.solution (A : Submodule (𝓞 K) K) :
    A.map ((LinearMap.id : K →ₗ[K] K).restrictScalars (𝓞 K)) = A := by
  first
    | (ext x; simp)
    | exact Submodule.map_id A
end Formalism.EigenvalueLevelCeiling
