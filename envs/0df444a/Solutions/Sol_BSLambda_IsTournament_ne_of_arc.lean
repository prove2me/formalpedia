-- Prove2me | solution 1 for BSLambda.IsTournament.ne_of_arc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:47:49.405582+00:00
-- url     : https://prove2.me/submissions/7168d8c4-f6c3-4054-8c3f-5c952483b95f

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
theorem _root_.solution (hij : Arc i j) : i ≠ j := by
  rintro rfl
  simp [h.arc_self] at hij
end BSLambda.IsTournament
