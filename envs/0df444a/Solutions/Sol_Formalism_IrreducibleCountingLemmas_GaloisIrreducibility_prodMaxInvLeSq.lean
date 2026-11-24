-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.prodMaxInvLeSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:16:10.786256+00:00
-- url     : https://prove2.me/submissions/5732d557-b15b-44d3-81ab-80b73b9dcba9

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_stab_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_good_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : LemmaP := by
  intro N a ha haN
  have key : ∀ σ : Equiv.Perm (Fin N),
      2 * (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) + (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card ≤ 2 * (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
    intro σ
    have hsub : ((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y) ⊆ ((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A) := by
      intro A hA
      simp only [Finset.mem_filter] at hA ⊢
      exact ⟨hA.1, hA.2.1⟩
    have hle := Finset.card_le_card hsub
    split_ifs with hX
    · obtain ⟨A0, hA0c, hA0⟩ := hX
      have h1 : 1 ≤ (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
        apply Finset.card_pos.mpr
        exact ⟨A0, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hA0c⟩, hA0⟩⟩
      by_cases hg : (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card = 0
      · omega
      · obtain ⟨A, hA⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hg)
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hA
        obtain ⟨⟨-, hAc⟩, hinv, ⟨x, hxA, hx⟩, ⟨y, hyA, hy⟩⟩ := hA
        have hyE : y ∉ A.erase x := fun h => hyA (Finset.mem_of_mem_erase h)
        have h2 : 1 < (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card := by
          rw [Finset.one_lt_card]
          refine ⟨A, ?_, insert y (A.erase x), ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hAc⟩, hinv⟩
          · simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
            refine ⟨?_, ?_⟩
            · rw [Finset.card_insert_of_notMem hyE, Finset.card_erase_of_mem hxA]
              have : 1 ≤ A.card := Finset.card_pos.mpr ⟨x, hxA⟩
              omega
            · intro z hz
              rcases Finset.mem_insert.mp hz with rfl | hz
              · rw [hy]
                exact Finset.mem_insert_self _ _
              · have hzA := Finset.mem_of_mem_erase hz
                have hzx := Finset.ne_of_mem_erase hz
                apply Finset.mem_insert_of_mem
                refine Finset.mem_erase.mpr ⟨?_, hinv z hzA⟩
                intro h
                apply hzx
                apply σ.injective
                rw [h, hx]
          · intro h
            apply hyA
            rw [h]
            exact Finset.mem_insert_self _ _
        omega
    · omega
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (univ : Finset (Equiv.Perm (Fin N)))) => key σ)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hX : ∑ σ : Equiv.Perm (Fin N), (if (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A) then 1 else 0) =
      ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∃ A : Finset (Fin N), A.card = a ∧ ∀ x ∈ A, σ x ∈ A))).card :=
    (Finset.card_filter _ _).symm
  have hs1 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => ∀ x ∈ A, σ x ∈ A)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hs2 : ∑ σ : Equiv.Perm (Fin N), (((univ : Finset (Fin N)).powersetCard a).filter (fun A => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card =
      ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hfac : ∑ _A ∈ ((univ : Finset (Fin N)).powersetCard a), a.factorial * (N - a).factorial = N.factorial := by
    rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial haN.le
  have hinv : ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => ∀ x ∈ A, σ x ∈ A)).card ≤ N.factorial := by
    rw [← hfac]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_stab_le A
    rwa [hA.2] at this
  have hgood : N.factorial ≤ 4 * ∑ A ∈ ((univ : Finset (Fin N)).powersetCard a), ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧ (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    rw [← hfac, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    rw [Finset.mem_powersetCard] at hA
    have := card_good_ge A (by omega) (by omega)
    rwa [hA.2] at this
  rw [hX, hs1, hs2] at hsum
  omega
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
