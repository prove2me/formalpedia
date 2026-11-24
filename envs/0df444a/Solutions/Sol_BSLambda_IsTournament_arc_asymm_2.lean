-- Prove2me | solution 2 for BSLambda.IsTournament.arc_asymm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:52:26.621945+00:00
-- url     : https://prove2.me/submissions/31c20406-c30c-42e0-966d-baa1b0c44ae6

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_arc_eq_false_of_arc

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
theorem _root_.solution (hij : Arc i j) : ¬ Arc j i :=
  Bool.eq_false_iff.mp (h.arc_eq_false_of_arc hij)
end BSLambda.IsTournament
