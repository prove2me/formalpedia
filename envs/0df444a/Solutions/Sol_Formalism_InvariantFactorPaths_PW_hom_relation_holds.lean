-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.hom_relation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:44:11.743107+00:00
-- url     : https://prove2.me/submissions/9587abec-e477-4a8f-80f6-f9d365d663b1

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_homAct_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution : HomRel := by
  intro K V W ι _ _ _ _ _ _ EV EW hV hW
  unfold GlRel at *
  intro a b c d
  ext φ x
  have h1 := LinearMap.congr_fun (hW a b c d) (φ x)
  have h2 := congrArg φ (LinearMap.congr_fun (hV a b c d) x)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, homAct_apply, map_sub] at h1 h2 ⊢
  split_ifs at h1 h2 ⊢ <;>
    simp only [LinearMap.zero_apply, map_zero, homAct_apply, sub_zero, zero_sub, map_neg, LinearMap.sub_apply, map_sub] at h1 h2 ⊢ <;>
    rw [eq_add_of_sub_eq h1, eq_add_of_sub_eq h2] <;> abel
end Formalism.InvariantFactorPaths.PW
