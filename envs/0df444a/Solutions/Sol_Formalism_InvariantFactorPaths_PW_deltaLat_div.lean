-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.deltaLat_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:56:16.832024+00:00
-- url     : https://prove2.me/submissions/a5423adb-9e45-42ed-acb6-08a792a53cdf

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
theorem _root_.solution (G : GlW ℚ_[p] V n) (s : Set V) : DivStable G.E (DeltaLat p G s) := by
  intro a b hab k x hx
  rw [DeltaLat, AddSubgroup.mem_sInf] at hx ⊢
  exact fun L hL => hL.2.2 a b hab k x (hx L hL)
end Formalism.InvariantFactorPaths.PW
