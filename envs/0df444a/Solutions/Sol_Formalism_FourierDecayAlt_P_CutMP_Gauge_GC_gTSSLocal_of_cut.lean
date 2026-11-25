-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTSSLocal_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:30:37.39393+00:00
-- url     : https://prove2.me/submissions/af59be2c-a8ea-48e2-9222-b497e5abd7ef

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLocalCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSLocalCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : GTSSLocalOfCut := by
  intro hRT hDZ hSS hMat Wp Wq _ _ _ _ _ _ P Bs X d hH e he _
  have hT := hRT Wp Wq P Bs hH.1 hH.2.1 hH.2.2.1 X
  have hSl : ∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b) := fun Y a b =>
    hDZ Wp Wq P Bs hH.1 _ (hT Y a b)
  exact hMat Wp Wq P Bs X d hH e he (hSS Wp Wq P Bs X d hH hSl)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
