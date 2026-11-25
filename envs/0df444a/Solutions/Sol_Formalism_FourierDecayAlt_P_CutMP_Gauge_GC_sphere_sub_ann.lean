-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.sphere_sub_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:59:25.631783+00:00
-- url     : https://prove2.me/submissions/6bbb436a-f465-41d7-b41c-cb75dd95f4f8

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolCut

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
theorem _root_.solution (P : M.Par) {R : ℝ} (hR0 : 0 < R) (hR : P.TT < R ^ 2) :
    Metric.sphere (0 : ℂ) R ⊆ Ann P := by
  intro w hw
  have h : ‖w‖ = R := by simpa using hw
  show P.TT < Complex.normSq w
  rw [Complex.normSq_eq_norm_sq, h]
  exact hR
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
