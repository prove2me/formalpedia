-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.sep_of_four
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:18:46.336309+00:00
-- url     : https://prove2.me/submissions/1fbe1d79-4577-4b8e-95ca-4313c6720951

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
theorem _root_.solution {x y : C.Letter} (h : 4 < |x.2 - y.2|) : Sep x y := by
  intro δ h1 h2
  have hδ1 : (-2 : ℝ) ≤ δ := by exact_mod_cast h1
  have hδ2 : (δ : ℝ) ≤ 2 := by exact_mod_cast h2
  rcases lt_abs.mp h with h | h
  · exact lt_abs.mpr (Or.inl (by linarith))
  · exact lt_abs.mpr (Or.inr (by linarith))
end Formalism.FourierDecayAlt.P.PBD
