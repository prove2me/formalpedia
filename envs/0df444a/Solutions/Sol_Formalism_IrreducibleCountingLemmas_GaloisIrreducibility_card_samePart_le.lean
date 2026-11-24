-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_samePart_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:49.08315+00:00
-- url     : https://prove2.me/submissions/a47d7c35-9a94-4065-8d39-4a95e1f411db

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CoeffZeroNeZeroOfIrreducible
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_nthRootsFinset_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_lpow_order_iff
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_to_part_eq_iff
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {l n : ℕ} (hl : l.Prime) (hn : n ≠ 0) (w : L) (S : Finset L)
    (hS : ∀ x ∈ S, x ^ n = 1 ∧ primeToPart l x = w) : S.card ≤ l ^ padicValNat l n := by
  classical
  rcases S.eq_empty_or_nonempty with hS0 | ⟨x0, hx0⟩
  · simp [hS0]
  obtain ⟨hx0n, hx0w⟩ := hS x0 hx0
  have hx0ne : x0 ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hx0n
    exact zero_ne_one hx0n
  have hfin : ∀ x : L, x ^ n = 1 → IsOfFinOrder x := fun x hx =>
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hx⟩
  have hmap : ∀ x ∈ S, x * x0⁻¹ ∈ nthRootsFinset (l ^ padicValNat l n) (1 : L) := by
    intro x hx
    obtain ⟨hxn, hxw⟩ := hS x hx
    obtain ⟨a, ha⟩ := (prime_to_part_eq_iff L l x x0 hl (hfin x hxn) (hfin x0 hx0n)).mp
      (hxw.trans hx0w.symm)
    have hz : (x * x0⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hxn, hx0n, inv_one, mul_one]
    have hza : (x * x0⁻¹) ^ (l ^ a) = 1 := by
      rw [mul_pow, inv_pow, ha, mul_inv_cancel₀ (pow_ne_zero _ hx0ne)]
    rw [mem_nthRootsFinset (pow_pos hl.pos _)]
    exact (lpow_order_iff hl hn _ hz).mp ⟨a, hza⟩
  calc S.card ≤ (nthRootsFinset (l ^ padicValNat l n) (1 : L)).card :=
        Finset.card_le_card_of_injOn (fun x => x * x0⁻¹) (fun x hx => hmap x hx)
          (fun a _ b _ h => mul_right_cancel₀ (inv_ne_zero hx0ne) h)
    _ ≤ l ^ padicValNat l n := card_nthRootsFinset_le _
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
