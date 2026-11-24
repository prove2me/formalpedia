-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.deltaLat_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:51.651605+00:00
-- url     : https://prove2.me/submissions/63278eb8-aa72-4f01-94e6-c3007d974138

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
theorem _root_.solution (G : GlW ℚ_[p] V n) (s : Set V) : ZpClosed p (DeltaLat p G s) := by
  intro c hc x hx
  rw [DeltaLat, AddSubgroup.mem_sInf] at hx ⊢
  exact fun L hL => hL.2.1 c hc x (hx L hL)
end Formalism.InvariantFactorPaths.PW
