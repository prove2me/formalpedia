-- Prove2me | solution 2 for BSLambda.IsTournament.disjoint_outNbrs_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:55:42.275802+00:00
-- url     : https://prove2.me/submissions/2a02c085-9200-4787-a405-35b2cc8297d8

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_arc_asymm
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_mem_inNbrs
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.mem_inNbrs

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable {Arc : ι → ι → Bool} {i j : ι}
namespace BSLambda
namespace IsTournament
theorem _root_.solution (h : IsTournament Arc) (v : ι) :
    Disjoint (outNbrs Arc v) (inNbrs Arc v) :=
  disjoint_left.2 fun _ hx hx' ↦ h.arc_asymm (mem_outNbrs.1 hx) (mem_inNbrs.1 hx')
end IsTournament
end BSLambda
