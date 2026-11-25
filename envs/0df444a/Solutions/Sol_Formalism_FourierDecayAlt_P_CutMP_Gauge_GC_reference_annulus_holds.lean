-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.reference_annulus_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:29:09.50619+00:00
-- url     : https://prove2.me/submissions/532d2905-8e4c-438f-862e-00d1d4d145c9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCRefCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCRefAn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
theorem _root_.solution : GTCRefAn := by
  intro TT α c hTT hα hre R hR hR2
  have hpt : ∀ θ : ℝ, TT < Complex.normSq (circleMap 0 R θ) := by
    intro θ
    have h1 : ‖circleMap 0 R θ‖ = R := by rw [norm_circleMap_zero, abs_of_pos hR]
    rw [Complex.normSq_eq_norm_sq, h1]
    exact hR2
  have hcα : Continuous (fun θ : ℝ => α (circleMap 0 R θ)) :=
    hα.continuousOn.comp_continuous (continuous_circleMap 0 R) hpt
  have hd : (fun θ : ℝ => deriv (circleMap 0 R) θ) = fun θ => circleMap 0 R θ * Complex.I := by
    funext θ
    exact deriv_circleMap 0 R θ
  have hF : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) := by
    have h2 : Continuous (fun θ : ℝ => deriv (circleMap 0 R) θ) := by
      rw [hd]
      exact (continuous_circleMap 0 R).mul continuous_const
    exact h2.smul hcα
  have key : ∀ θ : ℝ, Complex.imCLM (deriv (circleMap 0 R) θ • α (circleMap 0 R θ)) = c := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul, Complex.imCLM_apply]
    rw [← hre (circleMap 0 R θ) (hpt θ)]
    simp only [Complex.mul_im, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  unfold circleIntegral
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.intervalIntegral_comp_comm _ (hF.intervalIntegrable _ _)]
  simp only [key]
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
