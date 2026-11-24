-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.card_good_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:48.184201+00:00
-- url     : https://prove2.me/submissions/fede4274-1447-47e7-ad27-79a5c4cecfcc

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_fixed_ge

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
variable {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (A : Finset (Fin N)) (h1 : 1 ≤ A.card) (h2 : 1 ≤ N - A.card) :
    A.card.factorial * (N - A.card).factorial ≤
      4 * ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
        (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
  set P : Finset (Equiv.Perm {x // x ∈ A}) := univ.filter (fun s => ∃ x, s x = x) with hP
  set Q : Finset (Equiv.Perm {x // x ∉ A}) := univ.filter (fun s => ∃ x, s x = x) with hQ
  have hP1 : A.card.factorial ≤ 2 * P.card := by
    have := card_fixed_ge {x // x ∈ A} (by rw [Fintype.card_coe]; exact h1)
    rwa [Fintype.card_coe] at this
  have hc : Fintype.card {x // x ∉ A} = N - A.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  have hQ1 : (N - A.card).factorial ≤ 2 * Q.card := by
    have := card_fixed_ge {x // x ∉ A} (by rw [hc]; exact h2)
    rwa [hc] at this
  have hinj : (P ×ˢ Q).card ≤ ((univ : Finset (Equiv.Perm (Fin N))).filter (fun σ => (∀ x ∈ A, σ x ∈ A) ∧
      (∃ x ∈ A, σ x = x) ∧ ∃ y, y ∉ A ∧ σ y = y)).card := by
    refine Finset.card_le_card_of_injOn (fun q => Equiv.Perm.subtypeCongr q.1 q.2) ?_ ?_
    · rintro ⟨α, β⟩ hq
      simp only [Finset.mem_coe, Finset.mem_product, hP, hQ, Finset.mem_filter, Finset.mem_univ,
        true_and] at hq
      obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hq
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun z hz => ?_, ⟨x.1, x.2, ?_⟩, ⟨y.1, y.2, ?_⟩⟩
      · simp [Equiv.Perm.subtypeCongr.left_apply, hz]
      · simp [Equiv.Perm.subtypeCongr.left_apply, x.2, hx]
      · simp [Equiv.Perm.subtypeCongr.right_apply, y.2, hy]
    · rintro ⟨α, β⟩ _ ⟨α', β'⟩ _ he
      simp only at he
      have hA : α = α' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : α ⟨z, hz⟩ = α' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.left_apply, hz] using this
        rw [h']
      have hB : β = β' := by
        ext ⟨z, hz⟩
        have := congrArg (fun e : Equiv.Perm (Fin N) => e z) he
        have h' : (β ⟨z, hz⟩ : Fin N) = β' ⟨z, hz⟩ := by
          simpa [Equiv.Perm.subtypeCongr.right_apply, hz] using this
        rw [h']
      rw [hA, hB]
  rw [Finset.card_product] at hinj
  calc A.card.factorial * (N - A.card).factorial ≤ (2 * P.card) * (2 * Q.card) :=
        Nat.mul_le_mul hP1 hQ1
    _ = 4 * (P.card * Q.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hinj
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
