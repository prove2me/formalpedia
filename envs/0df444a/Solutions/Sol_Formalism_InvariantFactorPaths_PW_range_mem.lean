-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.range_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:01.987349+00:00
-- url     : https://prove2.me/submissions/6e90b296-9995-4f82-9ec0-b01964dfe0f3

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv

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
variable {K W ι : Type} [Field K] [AddCommGroup W] [Module K W] [DecidableEq ι]
variable {E : ι → ι → Module.End K W}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {a b : ι} (hab : a ≠ b) (x : W) :
    E a b x ∈ ⨆ (a : ι) (b : ι) (_ : a ≠ b), LinearMap.range (E a b) := Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
      (Submodule.mem_iSup_of_mem hab (LinearMap.mem_range_self _ _)))
end Formalism.InvariantFactorPaths.PW
