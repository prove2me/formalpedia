-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.gTCLocal_of_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:20.342367+00:00
-- url     : https://prove2.me/submissions/72d93049-f7ae-48b8-a4c1-606ed060f892

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLocalCut

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
theorem _root_.solution : GTCLocalOfCut := by
  intro hT hN hF Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk
  have hRT := hT Wp Wq P Bs hH.1 hH.2.1 hH.2.2.1 X
  obtain ⟨h1, h2⟩ := hN Wp Wq P Bs X d hH hRT e he hk
  exact hF Wp Wq P Bs X d hH e he hk h1 h2
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
