-- Prove2me | solution 1 for BSLambda.IsTournament.arc_eq_false_of_arc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:52:01.632365+00:00
-- url     : https://prove2.me/submissions/b17087ca-6576-46a6-b6ba-6091ab0f51e7

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc

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
theorem _root_.solution (hij : Arc i j) : Arc j i = false := by
  rw [h.arc_eq_not_arc (h.ne_of_arc hij).symm, hij, Bool.not_true]
end BSLambda.IsTournament
