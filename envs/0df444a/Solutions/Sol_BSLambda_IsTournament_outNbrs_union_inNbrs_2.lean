-- Prove2me | solution 2 for BSLambda.IsTournament.outNbrs_union_inNbrs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T00:56:06.123286+00:00
-- url     : https://prove2.me/submissions/2e2fc39c-440b-42c6-97ea-a9eb463215e8

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Fintype.Card
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc
public import Theorems.Thm_BSLambda_IsTournament_arc_or_arc
public import Theorems.Thm_BSLambda_mem_outNbrs
public import Theorems.Thm_BSLambda_mem_inNbrs
public import Theorems.Thm_BSLambda_mem_commonOut
public import Theorems.Thm_BSLambda_mem_commonIn
public import Theorems.Thm_BSLambda_mem_middles
attribute [local simp] BSLambda.mem_outNbrs
attribute [local simp] BSLambda.mem_inNbrs
attribute [local simp] BSLambda.mem_commonOut
attribute [local simp] BSLambda.mem_commonIn
attribute [local simp] BSLambda.mem_middles

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Finset
variable {ι : Type*}
variable [Fintype ι]
variable [DecidableEq ι]
variable {Arc : ι → ι → Bool} {i j l u v : ι}
open BSLambda.IsTournament
variable (h : IsTournament Arc)
include h
namespace BSLambda.IsTournament
theorem _root_.solution (v : ι) : outNbrs Arc v ∪ inNbrs Arc v = univ.erase v := by
  ext x
  simp only [mem_union, mem_outNbrs, mem_inNbrs, mem_erase, mem_univ, and_true]
  exact ⟨fun hx ↦ hx.elim (fun hx ↦ (h.ne_of_arc hx).symm) h.ne_of_arc,
    fun hx ↦ h.arc_or_arc hx.symm⟩
end BSLambda.IsTournament
