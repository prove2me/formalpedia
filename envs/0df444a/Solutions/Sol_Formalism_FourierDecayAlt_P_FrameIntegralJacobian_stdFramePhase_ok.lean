-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.stdFramePhase_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:02:51.191385+00:00
-- url     : https://prove2.me/submissions/8cf22e84-dca4-4cc3-b8a6-a778bf0f979a

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
theorem _root_.solution : StdFramePhase := by
  unfold StdFramePhase
  intro ka a b ha hb
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  have hab : a' + 1 + (b' + 1) - 2 = b' + a' := by omega
  have hconj : starRingEnd ℂ (Complex.I * ka) = Complex.I⁻¹ * ka := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.inv_I]
  have hz : Complex.I ^ (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = Complex.I ^ b' / Complex.I ^ a' := by
    rw [show (((b' + 1 : ℕ) : ℤ) - ((a' + 1 : ℕ) : ℤ)) = (b' : ℤ) - (a' : ℤ) by push_cast; ring,
      zpow_sub₀ Complex.I_ne_zero, zpow_natCast, zpow_natCast]
  simp only [Nat.add_sub_cancel]
  rw [hab, hconj, mul_pow, mul_pow, inv_pow, pow_add, hz]
  ring
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
