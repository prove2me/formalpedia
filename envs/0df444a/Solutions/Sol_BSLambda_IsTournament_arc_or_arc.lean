-- Prove2me | solution 1 for BSLambda.IsTournament.arc_or_arc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:48:11.754438+00:00
-- url     : https://prove2.me/submissions/f571c390-7ef8-4652-a56f-de3d06e50929

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
theorem _root_.solution (hij : i ≠ j) : Arc i j ∨ Arc j i := by
  cases hb : Arc j i <;> simp [h.arc_eq_not_arc hij, hb]
end BSLambda.IsTournament
