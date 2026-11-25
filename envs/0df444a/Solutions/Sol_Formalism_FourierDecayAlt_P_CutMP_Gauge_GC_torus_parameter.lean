-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.torus_parameter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:56:27.034831+00:00
-- url     : https://prove2.me/submissions/445c9188-a323-4fdf-950e-5be9fdad1875

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA

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
theorem _root_.solution : GTCTT := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH
  have hOK : P.OK := hH.1.1
  show 0 ≤ P.T * P.T'
  exact (mul_pos hOK.T_pos hOK.T'_pos).le
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
