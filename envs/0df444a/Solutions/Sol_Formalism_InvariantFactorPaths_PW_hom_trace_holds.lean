-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.hom_trace_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:01.968617+00:00
-- url     : https://prove2.me/submissions/5cfe968f-5961-4a0a-8419-c6a00ae1d44d

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds

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
theorem _root_.solution : HomTrace := by
  intro K V ι _ _ _ _ _ EV ψ hψ
  have h : (⨆ a, ⨆ b, ⨆ (_ : a ≠ b), LinearMap.range (homAct EV EV a b)) ≤
      LinearMap.ker (LinearMap.trace K V) := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_
    rintro _ ⟨φ, rfl⟩
    rw [LinearMap.mem_ker]
    show LinearMap.trace K V (EV a b * φ - φ * EV a b) = 0
    rw [map_sub, LinearMap.trace_mul_comm, sub_self]
  exact LinearMap.mem_ker.mp (h hψ)
end Formalism.InvariantFactorPaths.PW
