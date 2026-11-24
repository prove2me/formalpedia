-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.position_insertion_free_compat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:30.881575+00:00
-- url     : https://prove2.me/submissions/77d07991-1619-448e-82a7-e7ccac2cee86

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_free
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Wd.InsFree := by
  intro K A S _ _ _ _ _ _ _ _ a M
  exact ⟨fun c hc hM => Wd1.ins_free hc M hM, fun b hb hbM => Wd1.ins_comm a M b hb hbM⟩
end Formalism.FourierDecayAlt.P
