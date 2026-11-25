-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.sep_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:47.39216+00:00
-- url     : https://prove2.me/submissions/df83afcd-cbed-4042-8cfa-d4c486e2b96e

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RoomOffGridSymmetric
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtOfAdmissibleList

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution {x y : C.Letter} (h : Sep x y) : Sep y x := by
  intro δ h1 h2
  have h' := h (-δ) (by omega) (by omega)
  rw [show y.2 - x.2 + (δ : ℝ) = -(x.2 - y.2 + ((-δ : ℤ) : ℝ)) by push_cast; ring, abs_neg]
  exact h'
end Formalism.FourierDecayAlt.P.PBD
