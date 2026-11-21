-- Prove2me | solution 1 for Corless.corless
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:49:36.942983+00:00
-- url     : https://prove2.me/submissions/e45b8b4c-4ff6-44d2-a11b-8ea817373372

module
public import Mathlib.Algebra.BigOperators.Intervals
public import Definitions.Def_LeanPool_CorlessNilpotent_Parity
public import Definitions.Def_LeanPool_CorlessNilpotent_Main
public import Theorems.Thm_Corless_one_of_fam
public import Theorems.Thm_Corless_fam_of_one
public import Theorems.Thm_Corless_dimension


set_option autoImplicit true
@[expose] public section
public section
open Polynomial Finset
open Corless
namespace Corless
theorem _root_.solution {s : ℕ → ℤ} {m : ℕ} (hs : IsSign s m) (hm : 1 ≤ m) :
    Dv s m = 1 ↔ ∃ k, m = 2 ^ (k + 1) - 1 ∧ Fam k s := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := dimension hs hm h
    exact ⟨k, rfl, fam_of_one k hs h⟩
  · rintro ⟨k, rfl, hk⟩
    exact one_of_fam k hk
end Corless
