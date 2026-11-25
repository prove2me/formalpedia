-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.fderiv_om_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:37:34.336794+00:00
-- url     : https://prove2.me/submissions/a5613b00-2c49-4b60-876a-c2b71f6ea7bf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FderivDecomp
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BasePointMemHalfPlane
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_bet

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
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) {w : ℂ} (hw : w ∈ Hh TT) (h k : ℂ) :
    fderiv ℝ (om α) w h k = 2 * (fderiv ℝ (bet α) w h * k).im := by
  have hb := hasFDerivAt_bet hα hw
  have hom : HasFDerivAt (om α) (omL.comp (fderiv ℝ (bet α) w)) w :=
    omL.hasFDerivAt.comp w hb.differentiableAt.hasFDerivAt
  rw [hom.fderiv]
  simp [omL, two_smul, two_mul]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
