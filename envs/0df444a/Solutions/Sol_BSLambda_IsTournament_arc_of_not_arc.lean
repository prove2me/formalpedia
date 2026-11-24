-- Prove2me | solution 1 for BSLambda.IsTournament.arc_of_not_arc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:48:28.225882+00:00
-- url     : https://prove2.me/submissions/3d9b2785-0be7-45f6-9534-558becd60d34

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
open BSLambda.IsTournament
variable {Arc : ι → ι → Bool} (h : IsTournament Arc) {i j : ι}
include h
namespace BSLambda.IsTournament
theorem _root_.solution (hij : i ≠ j) (hji : Arc j i = false) : Arc i j := by
  rw [h.arc_eq_not_arc hij, hji, Bool.not_false]
end BSLambda.IsTournament
