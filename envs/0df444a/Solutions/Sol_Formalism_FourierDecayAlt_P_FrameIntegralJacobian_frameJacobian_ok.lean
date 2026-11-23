-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.frameJacobian_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:48.272801+00:00
-- url     : https://prove2.me/submissions/4d0990e1-1f46-45f9-9ffd-6330b5d946b2

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
theorem _root_.solution : FrameJacobian := by
  unfold FrameJacobian
  intro ka m g hka
  have hk0 : ka ≠ 0 := hka.ne'
  have hk0c : (ka : ℂ) ≠ 0 := by exact_mod_cast hk0
  have hcv : ∫ x : ℂ, ((‖ka • x‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • x)
      = |(ka ^ 2)⁻¹| • ∫ x : ℂ, ((‖x‖ ^ (2 * m) : ℝ) : ℂ) * g x := by
    have h := MeasureTheory.Measure.integral_comp_smul
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℂ))
      (fun z : ℂ => ((‖z‖ ^ (2 * m) : ℝ) : ℂ) * g z) ka
    rw [Complex.finrank_real_complex] at h
    exact h
  have hpt : ∀ c : ℂ, ((‖c‖ ^ (2 * m) : ℝ) : ℂ) * g ((ka : ℂ) * c)
      = ((ka ^ (2 * m))⁻¹ : ℝ) • (((‖ka • c‖ ^ (2 * m) : ℝ) : ℂ) * g (ka • c)) := by
    intro c
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hka, mul_pow, Complex.real_smul, Complex.real_smul]
    push_cast
    rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hk0c), one_mul]
  have hreal : ka ^ (2 * m + 2) * ((ka ^ (2 * m))⁻¹ * (ka ^ 2)⁻¹) = 1 := by
    rw [pow_add, mul_mul_mul_comm, mul_inv_cancel₀ (pow_ne_zero _ hk0),
      mul_inv_cancel₀ (pow_ne_zero _ hk0), one_mul]
  simp_rw [hpt]
  rw [MeasureTheory.integral_smul, hcv, smul_smul, abs_of_pos (inv_pos.mpr (pow_pos hka 2)), Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul, hreal, Complex.ofReal_one, one_mul]
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
