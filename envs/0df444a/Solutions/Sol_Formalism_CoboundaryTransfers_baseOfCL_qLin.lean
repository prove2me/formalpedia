-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.baseOfCL_qLin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:06.36828+00:00
-- url     : https://prove2.me/submissions/431ee9a2-45f0-429f-813b-9ec1f9d504f1

import Definitions.Def_Formalism_CoboundaryTransfers_StatementBridge
import Definitions.Def_Formalism_WachModuleLifts_WachModuleProofs_WachModuleStatementHolds
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_BridgeCL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
open Formalism
namespace Formalism.CoboundaryTransfers
theorem _root_.solution {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (B : CL.W.Base p A) : (baseOfCL B).QLin := by
  show B.q = B.π₀ + ((p : ℕ) : A)
  rw [B.hq, map_natCast]
end Formalism.CoboundaryTransfers
