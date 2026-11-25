-- Prove2me | solution 2 for Formalism.FourierDecayAlt.P.PBD.two_lt_of_four_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:45:19.776285+00:00
-- url     : https://prove2.me/submissions/10f7196a-ede3-4a92-9b65-44c65cdd9001

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution {y p : ℝ} (h : 4 < |y - p|) : 2 < |y + 1 - p| := by
  rcases lt_abs.mp h with h | h
  · exact lt_abs.mpr (Or.inl (by linarith))
  · exact lt_abs.mpr (Or.inr (by linarith))
end Formalism.FourierDecayAlt.P.PBD
