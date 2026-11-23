-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PermutationFixedPoints.card_good_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:39.790856+00:00
-- url     : https://prove2.me/submissions/4371e7b2-e1bb-41be-87cc-50bf452ddde1

import Definitions.Def_Formalism_CyclotomicNorms_DiscardKernel
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_TwoMulNumDerangementsLeFactorial
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_card_perm_with_fixed
import Theorems.Thm_Formalism_CyclotomicNorms_PermutationFixedPoints_inv_exchange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.PermutationFixedPoints
namespace Formalism.CyclotomicNorms.PermutationFixedPoints
theorem _root_.solution (N a : ℕ) (ha : 0 < a) (haN : a < N) (S : Finset (Fin N))
    (hS : S.card = a) :
    a.factorial * (N - a).factorial ≤
      4 * (univ.filter (fun σ : Equiv.Perm (Fin N) =>
        (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ)).card := by
  set P := univ.filter (fun p : Equiv.Perm {x // x ∈ S} => ∃ x, p x = x) with hPdef
  set Q := univ.filter (fun q : Equiv.Perm {x // x ∉ S} => ∃ y, q y = y) with hQdef
  have hcS : Fintype.card {x // x ∈ S} = a := by rw [Fintype.card_coe, hS]
  have hcT : Fintype.card {x // x ∉ S} = N - a := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin, hS]
  have hP := card_perm_with_fixed (α := {x // x ∈ S}) (by omega)
  have hQ := card_perm_with_fixed (α := {x // x ∉ S}) (by omega)
  rw [hcS] at hP
  rw [hcT] at hQ
  have hsub : (P ×ˢ Q).image (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S)) ⊆
      univ.filter (fun σ : Equiv.Perm (Fin N) =>
        (∀ x, σ x ∈ S ↔ x ∈ S) ∧ 2 ≤ numInv N a σ) := by
    intro σ hσ
    simp only [Finset.mem_image, Finset.mem_product, hPdef, hQdef, Finset.mem_filter,
      Finset.mem_univ, true_and] at hσ
    obtain ⟨⟨p, q⟩, ⟨⟨x, hx⟩, ⟨y, hy⟩⟩, rfl⟩ := hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hinv : ∀ z, (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S) (p, q)) z ∈ S ↔ z ∈ S := by
      intro z
      rw [Equiv.Perm.subtypeCongrHom_apply]
      by_cases hz : z ∈ S
      · rw [Equiv.Perm.subtypeCongr.left_apply _ _ hz]
        simp [hz, (p ⟨z, hz⟩).2]
      · rw [Equiv.Perm.subtypeCongr.right_apply _ _ hz]
        simp [hz, (q ⟨z, hz⟩).2]
    have hxσ : (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S) (p, q)) (x : Fin N) = x := by
      rw [Equiv.Perm.subtypeCongrHom_apply, Equiv.Perm.subtypeCongr.left_apply _ _ x.2]
      simp [hx]
    have hyσ : (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S) (p, q)) (y : Fin N) = y := by
      rw [Equiv.Perm.subtypeCongrHom_apply, Equiv.Perm.subtypeCongr.right_apply _ _ y.2]
      simp [hy]
    refine ⟨hinv, ?_⟩
    have hy' : (y : Fin N) ∉ S.erase x := fun h => y.2 (Finset.mem_of_mem_erase h)
    refine Finset.one_lt_card.2 ⟨S, ?_, insert (y : Fin N) (S.erase x), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, hS⟩, hinv⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, inv_exchange _ S hinv x y hxσ hyσ⟩
      rw [Finset.card_insert_of_notMem hy', Finset.card_erase_of_mem x.2, hS]
      omega
    · intro h
      have hm : (y : Fin N) ∈ insert (y : Fin N) (S.erase x) := Finset.mem_insert_self _ _
      rw [← h] at hm
      exact y.2 hm
  have hcard : ((P ×ˢ Q).image (Equiv.Perm.subtypeCongrHom (fun x => x ∈ S))).card =
      P.card * Q.card := by
    rw [Finset.card_image_of_injective _ (Equiv.Perm.subtypeCongrHom_injective _),
      Finset.card_product]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  calc a.factorial * (N - a).factorial ≤ (2 * P.card) * (2 * Q.card) := Nat.mul_le_mul hP hQ
    _ = 4 * (P.card * Q.card) := by ring
    _ ≤ _ := Nat.mul_le_mul_left 4 hle
end Formalism.CyclotomicNorms.PermutationFixedPoints
