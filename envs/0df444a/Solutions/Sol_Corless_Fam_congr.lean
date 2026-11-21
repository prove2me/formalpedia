-- Prove2me | solution 1 for Corless.Fam_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:26.914298+00:00
-- url     : https://prove2.me/submissions/c1bfda2b-6379-4977-a8e1-ca6fe55f643d

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_entrySign_one
public import Theorems.Thm_Corless_folded_edges
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
theorem _root_.solution : ∀ (k : ℕ) {s t : ℕ → ℤ}, (∀ i < 2 ^ (k + 1) - 2, s i = t i) →
    (Fam k s ↔ Fam k t)
  | 0, _, _, _ => by simp [Fam]
  | k + 1, s, t, h => by
      change ∀ i < 2 ^ (k + 2) - 2, s i = t i at h
      rw [folded_edges k] at h
      simp only [Fam, IsFolded]
      rw [h (2 ^ (k + 1) - 2 + 1) (by omega), h (2 ^ (k + 1) - 2) (by omega),
        solution k (fun i hi => h i (by omega))]
      constructor
      · rintro ⟨⟨h1, h2'⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        rw [← h _ (by omega), ← h i (by omega)]
        exact h2' i hi
      · rintro ⟨⟨h1, h2'⟩, h3⟩
        refine ⟨⟨h1, fun i hi => ?_⟩, h3⟩
        rw [h _ (by omega), h i (by omega)]
        exact h2' i hi
end Corless
