-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameIntegral_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:47.93201+00:00
-- url     : https://prove2.me/submissions/d9a565ee-7788-41ff-bdf1-68f6d51d4c67

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian
theorem _root_.solution : FrameIntegral := by
  unfold FrameIntegral
  intro ka de Cst ph pht Rt R hka hde hph hRt hR
  have hk0 : ka ≠ 0 := hka.ne'
  have hcv : ∫ x : ℂ, pht (ka • x) = |(ka ^ 2)⁻¹| • ∫ x : ℂ, pht x := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ)) pht ka
    rw [Complex.finrank_real_complex] at h
    exact h
  have hfun : ∀ c : ℂ, ph c * (de : ℂ) = (Cst * ka ^ 2 : ℝ) • pht (ka • c) := by
    intro c
    rw [hph c, Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  simp_rw [hfun]
  rw [MeasureTheory.integral_smul, hcv, smul_smul, hRt, hR, abs_of_pos (inv_pos.mpr (pow_pos hka 2)),
    Complex.real_smul, mul_assoc Cst, mul_inv_cancel₀ (pow_ne_zero 2 hk0), mul_one]
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
