-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph.circleMap_mem_annT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:06.597106+00:00
-- url     : https://prove2.me/submissions/69bd223e-4d30-47c1-bda5-21fc5de285cb

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
theorem _root_.solution {TT R : ℝ} (hR : TT < R ^ 2) (θ : ℝ) : circleMap 0 R θ ∈ AnnT TT := by
  show TT < Complex.normSq (circleMap 0 R θ)
  rw [Complex.normSq_eq_norm_sq, norm_circleMap_zero, sq_abs]
  exact hR
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
