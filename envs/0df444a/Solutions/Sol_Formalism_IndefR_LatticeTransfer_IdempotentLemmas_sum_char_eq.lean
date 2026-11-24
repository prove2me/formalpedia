-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.sum_char_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:04.097707+00:00
-- url     : https://prove2.me/submissions/9bb314bf-9f1a-4fe3-a95d-4ed779bd3292

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.IndefR.LatticeTransfer.IdempotentLemmas
theorem _root_.solution [CharZero K] {T U : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    ∑ x : G, charOf τ x⁻¹ * charOf σ x =
      (Fintype.card G : K) * finrank K (Representation.IntertwiningMap τ σ) := by
  have hc : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have : Invertible (Nat.card G : K) := invertibleOfNonzero hc
  have h := Representation.card_inv_mul_sum_char_mul_char_eq_finrank τ σ
  rw [← Nat.card_eq_fintype_card, ← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [mul_comm]
  rfl
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
