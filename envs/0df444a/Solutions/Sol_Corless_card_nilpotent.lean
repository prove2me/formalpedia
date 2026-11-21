-- Prove2me | solution 1 for Corless.card_nilpotent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:51:47.740954+00:00
-- url     : https://prove2.me/submissions/f8700957-bf36-4be9-98cd-0ef9a56b8e6d

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_CorlessVec_length_eq
public import Theorems.Thm_Corless_CorlessVec_mem
public import Theorems.Thm_Corless_corless_conjecture
public import Theorems.Thm_Corless_mem_vecs
public import Theorems.Thm_Corless_card_vecs
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_entrySign_one
public import Theorems.Thm_Corless_two_le_pow
attribute [local simp] Corless.Dv_one
attribute [local simp] Corless.Dv_zero
attribute [local simp] Corless.entrySign_I
attribute [local simp] Corless.entrySign_one



set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless
namespace Corless
theorem _root_.solution (k : ℕ) :
    {u : List ℂ | u.length = 2 ^ (k + 1) - 2 ∧ (∀ x ∈ u, x = 1 ∨ x = Complex.I) ∧
      IsNilpotent (T (u.length + 1) (fun i => u.getD i 1))}.ncard = 2 ^ k := by
  have hset : {u : List ℂ | u.length = 2 ^ (k + 1) - 2 ∧ (∀ x ∈ u, x = 1 ∨ x = Complex.I) ∧
      IsNilpotent (T (u.length + 1) (fun i => u.getD i 1))} = ↑(vecs k) := by
    ext u
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_vecs]
    constructor
    · rintro ⟨hlen, hu, hnil⟩
      obtain ⟨k', hk'⟩ := (corless_conjecture hu).mp hnil
      have hkk : k' = k := by
        have h1 := hk'.length_eq
        have := two_le_pow k
        have := two_le_pow k'
        have h2 : 2 ^ (k' + 1) = 2 ^ (k + 1) := by omega
        have := Nat.pow_right_injective le_rfl h2
        omega
      exact hkk ▸ hk'
    · intro h
      exact ⟨h.length_eq, h.mem, (corless_conjecture h.mem).mpr ⟨k, h⟩⟩
  rw [hset, Set.ncard_coe_finset, card_vecs]
end Corless
