-- Prove2me | solution 1 for Corless.mem_vecs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:43:29.7282+00:00
-- url     : https://prove2.me/submissions/a6db9490-5064-4c3e-a69f-529e29cdccf7

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors
public import Theorems.Thm_Corless_Dv_one
public import Theorems.Thm_Corless_Dv_zero
public import Theorems.Thm_Corless_entrySign_I
public import Theorems.Thm_Corless_entrySign_one
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
theorem _root_.solution (k : ℕ) : ∀ {u : List ℂ}, u ∈ vecs k ↔ CorlessVec k u := by
  induction k with
  | zero =>
      intro u
      simp only [vecs, Finset.mem_singleton]
      constructor
      · rintro rfl
        exact .base
      · intro h
        cases h
        rfl
  | succ k ih =>
      intro u
      simp only [vecs, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, ih]
      constructor
      · rintro ⟨v, hv, rfl | rfl⟩
        · exact .step₁ hv
        · exact .step₂ hv
      · intro h
        cases h with
        | step₁ hv => exact ⟨_, hv, Or.inl rfl⟩
        | step₂ hv => exact ⟨_, hv, Or.inr rfl⟩
end Corless
