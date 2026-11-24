-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.ptG_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:31:10.865195+00:00
-- url     : https://prove2.me/submissions/7fc1ed3e-5d47-49f0-bc1c-f863528238a1

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_det_ptMatN_app

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
theorem _root_.solution (TT : ℝ) (c : ℂ) (H : C.LPt) (n : ℕ) (hn : D.ptSize H = n) :
    D.ptG TT n (H ++ [(1, c)]) = Complex.normSq (D.ptMatN H n).det * (Complex.normSq c - TT) := by
  obtain ⟨h1, h2⟩ := det_ptMatN_app c H n hn
  unfold D.ptG
  rw [h1, h2, Complex.normSq_mul]
  ring
end Formalism.FourierDecayAlt.P.PBD
