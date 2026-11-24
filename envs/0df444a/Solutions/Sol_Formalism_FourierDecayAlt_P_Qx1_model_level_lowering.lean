-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx1.model_level_lowering
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:53.335329+00:00
-- url     : https://prove2.me/submissions/0fa6dd19-993d-4b9d-a595-dbcbbdfa0a2f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModelLevelMultiplier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Formalism.FourierDecayAlt.P.Qx1
namespace Formalism.FourierDecayAlt.P.Qx1
theorem _root_.solution (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.l0 Y = M.l0A P Y := by
  obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hGGi, hnab, -, -⟩ := hL
  simp only [R.LevelData.l0, M.l0A, hzb, hGGi, hnab]
end Formalism.FourierDecayAlt.P.Qx1
