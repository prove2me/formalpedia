-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.gaExponent_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:48.728696+00:00
-- url     : https://prove2.me/submissions/3a76ff98-2b13-44ef-b339-6de4d7eccd6f

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
theorem _root_.solution : GaExponent := by
  unfold GaExponent
  refine ⟨fun ka l M hM => ?_, fun r k hk => ?_⟩
  · rw [← pow_mul]
    congr 1
    obtain ⟨M', rfl⟩ : ∃ M', M = M' + 2 := ⟨M - 2, by omega⟩
    rcases Nat.eq_zero_or_pos l with hl | hl
    · subst hl
      simp
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have h1 : 2 * (l' + 1) - 2 = 2 * l' := by omega
      have h2 : 2 * (M' + 2 - 2) + 2 = 2 * (M' + 1) := by omega
      have h3 : l' + 1 - 1 = l' := by omega
      have h4 : M' + 2 - 1 = M' + 1 := by omega
      rw [h1, h2, h3, h4]
      ring
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h1 : k' + 1 - 1 = k' := by omega
    have h2 : k' + 1 + 1 - 1 = k' + 1 := by omega
    rw [h1, h2]
    ring
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
