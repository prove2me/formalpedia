-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.continuousOn_bet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:14:59.505881+00:00
-- url     : https://prove2.me/submissions/50b708a8-a5f2-4907-8aeb-974a98076b0c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaAtBasePointZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_contDiffOn_bet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    ContinuousOn (bet α) (Hh TT) := by
  exact (contDiffOn_bet hα).continuousOn
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
