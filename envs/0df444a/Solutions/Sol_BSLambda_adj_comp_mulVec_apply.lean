-- Prove2me | solution 1 for BSLambda.adj_comp_mulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:00.290854+00:00
-- url     : https://prove2.me/submissions/ff82c611-4dba-40cc-900b-bfebbd45543c

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_flipSet_prod_singleton
public import Theorems.Thm_BSLambda_adj_comp_flip
public import Theorems.Thm_BSLambda_adj_mulVec_apply


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (x : Input (W × V)) :
    (adj (comp f g) *ᵥ ψ) x
      = ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
          * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) := by
  rw [adj_mulVec_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [adj_mulVec_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [adj_comp_flip, flipSet_prod_singleton, mul_assoc]
end BSLambda
