-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.bSt_append_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:18.486257+00:00
-- url     : https://prove2.me/submissions/12bbe673-142c-4443-8b9f-1b3cd1633bbe

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.PBD
theorem _root_.solution (κ : ℝ) (h : C.LPt) (c : ℂ) : D.bSt κ (h ++ [(1, c)]) = D.bSt κ h := by
  simp [D.bSt]
end Formalism.FourierDecayAlt.P.PBD
