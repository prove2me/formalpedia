-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTConn_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:11:26.790147+00:00
-- url     : https://prove2.me/submissions/f1116d63-ab4d-4d17-83d1-cf1b9dfd3a98

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGenTransferCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut

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
theorem _root_.solution : GTConnOfCut := by
  intro hL hP hG Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk
  obtain ⟨A, B', hAB, hC⟩ := hL Wp Wq P Bs X d hH e he hk
  obtain ⟨u, hu⟩ := hP Wp Wq P Bs X d hH e he hk A B' hAB hC
  exact ⟨_, hG Wp Wq P Bs X d hH e he hk A B' u hAB hC hu⟩
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
