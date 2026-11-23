-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.scaleBeta_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:48.878629+00:00
-- url     : https://prove2.me/submissions/3ea4a19f-e1c4-4d48-b2c2-57957905a2f5

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
theorem _root_.solution : ScaleBeta := by
  unfold ScaleBeta
  intro ka Pp q r hka hq hP
  have hk0 : ka ≠ 0 := hka.ne'
  have e1 : Pp / (ka ^ (4 * r) * q) = Pp / q / (ka ^ (2 * r)) ^ 2 := by
    rw [← pow_mul, div_div, mul_comm q, show 2 * r * 2 = 4 * r by ring]
  have e2 : ka ^ (-(1 + 2 * r : ℤ)) = (ka * ka ^ (2 * r))⁻¹ := by
    rw [zpow_neg, ← pow_succ', show (1 + 2 * (r:ℤ)) = ((2 * r + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
  rw [e1, Real.sqrt_div (div_nonneg hP hq.le), Real.sqrt_sq (pow_nonneg hka.le (2 * r)), e2, mul_inv,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hk0, one_mul, div_eq_inv_mul]
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
