-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.blockPhase_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:50.095429+00:00
-- url     : https://prove2.me/submissions/d9dbbc0a-27a2-4eae-8e59-a46d77bad597

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
theorem _root_.solution : BlockPhase := by
  unfold BlockPhase
  intro s x
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h1 : Complex.I ^ ((s:ℤ) - 1 - 2 * x) = Complex.I ^ ((s:ℤ) - 1) * ((Complex.I ^ 2) ^ x)⁻¹ := by
    rw [sub_eq_add_neg ((s:ℤ) - 1), zpow_add₀ hI, zpow_neg, ← pow_mul]
    norm_cast
  rw [h1, Complex.I_sq, mul_assoc, inv_mul_cancel₀ (pow_ne_zero x (by norm_num : (-1:ℂ) ≠ 0)), mul_one]
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
