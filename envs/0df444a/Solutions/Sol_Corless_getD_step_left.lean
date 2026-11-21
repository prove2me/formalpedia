-- Prove2me | solution 1 for Corless.getD_step_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:42:14.615422+00:00
-- url     : https://prove2.me/submissions/c2ed43f7-c394-4d0e-bc26-da0c377e9c26

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
theorem _root_.solution (u : List ℂ) (a b : ℂ) {i : ℕ} (hi : i < u.length) :
    (foldVector u a b).getD i 1 = u.getD i 1 := by
  rw [foldVector, List.append_assoc, List.getD_append _ _ _ _ hi]
end Corless
