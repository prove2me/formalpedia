-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.subset_deltaLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:01.946104+00:00
-- url     : https://prove2.me/submissions/cb04e6d4-5dd5-4f96-b435-3274f9e2a896

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ}
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution (G : GlW ℚ_[p] V n) (s : Set V) : s ⊆ DeltaLat p G s := by
  intro x hx
  rw [SetLike.mem_coe, DeltaLat, AddSubgroup.mem_sInf]
  exact fun L hL => hL.1 hx
end Formalism.InvariantFactorPaths.PW
