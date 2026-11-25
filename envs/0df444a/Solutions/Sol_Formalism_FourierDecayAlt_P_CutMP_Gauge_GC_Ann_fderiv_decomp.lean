-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:04.24158+00:00
-- url     : https://prove2.me/submissions/a8f6d013-3fd1-402f-b33d-b44376b46205

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_clm_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (f : ℂ → ℂ) (ζ v : ℂ) :
    fderiv ℝ f ζ v = wZ f ζ * v + wZb f ζ * (starRingEnd ℂ v) := by
  unfold wZ wZb
  exact clm_decomp _ v
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
