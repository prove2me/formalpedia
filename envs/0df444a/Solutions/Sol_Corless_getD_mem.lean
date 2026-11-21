-- Prove2me | solution 1 for Corless.getD_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:27.393655+00:00
-- url     : https://prove2.me/submissions/d7b6c576-d64a-43c4-9d36-6e7f52f967c0

module
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Set.Card
public import Definitions.Def_LeanPool_CorlessNilpotent_Matrix
public import Definitions.Def_LeanPool_CorlessNilpotent_Vectors

set_option autoImplicit true
@[expose] public section
public section
open Polynomial
open Corless
namespace Corless
theorem _root_.solution {u : List ℂ} (hu : ∀ x ∈ u, x = 1 ∨ x = Complex.I) (i : ℕ) (hi : i < u.length) :
    u.getD i 1 = 1 ∨ u.getD i 1 = Complex.I := by
  rw [List.getD_eq_getElem _ _ hi]
  exact hu _ (List.getElem_mem hi)
end Corless
