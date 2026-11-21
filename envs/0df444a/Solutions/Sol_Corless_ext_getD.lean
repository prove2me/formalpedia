-- Prove2me | solution 1 for Corless.ext_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:42.986643+00:00
-- url     : https://prove2.me/submissions/91e62e19-5b45-409c-8d71-fcf6a8443ee3

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
theorem _root_.solution {l l' : List ℂ} (hl : l.length = l'.length)
    (h : ∀ i < l.length, l.getD i 1 = l'.getD i 1) : l = l' := by
  apply List.ext_getElem hl
  intro i h1 h2
  rw [← List.getD_eq_getElem _ 1 h1, ← List.getD_eq_getElem _ 1 h2]
  exact h i h1
end Corless
