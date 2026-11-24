-- Prove2me | solution 1 for Formalism.L2.G.card_quotient_extRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:01:36.031503+00:00
-- url     : https://prove2.me/submissions/adf6cda9-e316-4e43-ab02-c2456b4662e8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
noncomputable section
namespace Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
private theorem card_wittVector_quot_p_eq_card_field (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    Nat.card (WittVector p k ⧸ Ideal.span {(p : WittVector p k)}) = Nat.card k := by
  have hsurj : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := by
    intro r
    exact ⟨WittVector.teichmuller p r, WittVector.teichmuller_coeff_zero p r⟩
  have hker : RingHom.ker (WittVector.constantCoeff : WittVector p k →+* k) =
      Ideal.span {(p : WittVector p k)} := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton']
    constructor
    · intro hx
      by_cases h0 : x = 0
      · exact ⟨0, by rw [h0, zero_mul]⟩
      obtain ⟨m, b, hb0, hb⟩ := WittVector.exists_eq_pow_p_mul x h0
      cases m with
      | zero =>
        exfalso
        rw [pow_zero, one_mul] at hb
        exact hb0 (hb ▸ hx)
      | succ m => exact ⟨(p : WittVector p k) ^ m * b, by rw [hb]; ring⟩
    · rintro ⟨a, rfl⟩
      rw [map_mul, map_natCast, CharP.cast_eq_zero, mul_zero]
  rw [← hker]
  exact Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
end Formalism.L2.G
end
end

set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution : Nat.card (W2 p n ⧸ Ideal.span {(p : W2 p n)}) = p ^ (2 * n) := by
  rw [card_wittVector_quot_p_eq_card_field, Module.natCard_eq_pow_finrank (K := F1 p n),
    FiniteField.finrank_extension, GaloisField.card p n (NeZero.ne n), ← pow_mul, mul_comm]
end Formalism.L2.G
