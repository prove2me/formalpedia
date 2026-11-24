-- Prove2me | solution 1 for BSLambda.LLL.badVerts_injOn_type_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:11:43.748812+00:00
-- url     : https://prove2.me/submissions/1e82f7df-5c16-44f4-acb6-9ae68a723296

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_LLLBounds
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_GateExists
public import Theorems.Thm_BSLambda_LLL_exists_inr_of_badTy_eq_true

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
open Numerics Construction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ} {Arc : ι → ι → Bool}
namespace BSLambda.LLL
theorem _root_.solution (i : BadIdx Arc) :
    Set.InjOn badVerts
      (((nbr (badSupp (Arc := Arc)) i).filter fun j => badTy j = true) : Set (BadIdx Arc)) := by
  intro j hj k hk hjk
  rw [Finset.mem_coe] at hj hk
  obtain ⟨S, rfl⟩ := exists_inr_of_badTy_eq_true (Finset.mem_filter.mp hj).2
  obtain ⟨T, rfl⟩ := exists_inr_of_badTy_eq_true (Finset.mem_filter.mp hk).2
  exact congrArg Sum.inr (Subtype.ext hjk)
end BSLambda.LLL
