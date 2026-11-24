-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBD.isLocPt_toStd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:42.009835+00:00
-- url     : https://prove2.me/submissions/887abf4a-1b71-4a50-a6b9-a3d151b434d0

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_PBD_toStd_size__257163185415
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_toStd_ok_iff

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
theorem _root_.solution (r : ℕ) (g : ℝ) (hg : 0 < g) (p : C.LPt) (b i : ℕ) :
    D.IsLocPt (D.toStd r g b p) i ↔ D.IsLocPt p i := by
  unfold D.IsLocPt
  rw [toStd_ok_iff r g hg p b, toStd_size']
end Formalism.FourierDecayAlt.P.PBD
