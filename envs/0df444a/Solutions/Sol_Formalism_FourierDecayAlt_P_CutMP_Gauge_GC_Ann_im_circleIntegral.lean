-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.im_circleIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:45:21.664276+00:00
-- url     : https://prove2.me/submissions/81618f37-27f9-40de-aeca-4386bfd2b9ae

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaAtBasePointZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_cont_vert
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_circleIntegral_eq


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
theorem _root_.solution (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT)) :
    (circleIntegral α 0 (TT + 1)).im = ∫ θ in (0 : ℝ)..2 * Real.pi, (bet α (x0 TT + (θ : ℂ) * I)).re := by
  have hint : IntervalIntegrable (fun θ : ℝ => I * bet α (x0 TT + (θ : ℂ) * I)) MeasureTheory.volume
      0 (2 * Real.pi) :=
    (continuous_const.mul (cont_vert hTT hα)).intervalIntegrable _ _
  rw [circleIntegral_eq hTT, ← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hint]
  congr 1
  funext θ
  simp [Complex.mul_im]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
