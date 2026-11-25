-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.fnZ_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:58.634902+00:00
-- url     : https://prove2.me/submissions/bafb5f62-828d-4ff6-afa2-4db0bb1503f9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut

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
theorem _root_.solution (P : M.Par) {f g : ℂ → ℂ} (h : ∀ ζ ∈ Ann P, f ζ = g ζ) : fnZ P f = fnZ P g := by
  unfold fnZ
  congr 1
  funext q
  exact h _ q.2.2
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
