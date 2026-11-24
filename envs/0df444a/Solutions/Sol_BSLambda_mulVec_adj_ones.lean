-- Prove2me | solution 1 for BSLambda.mulVec_adj_ones
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:04.911679+00:00
-- url     : https://prove2.me/submissions/8a07cca8-cb31-459f-968a-a47e94abe5a6

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Theorems.Thm_BSLambda_biadj_eq_adj
public import Theorems.Thm_BSLambda_sum_ones_add_sum_zeros
public import Theorems.Thm_BSLambda_adj_eq_zero_of_apply_eq

section
@[expose] public section
namespace BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
private lemma sum_adj_mul_eq_zero_of_apply_eq (f : Input V → Bool) (v : Input V → ℝ) {b : Bool}
    {a : Input V} (ha : f a = b) : ∑ y : {y : Input V // f y = b}, adj f a y.1 * v y.1 = 0 := by
  refine Finset.sum_eq_zero fun y _ ↦ ?_
  rw [adj_eq_zero_of_apply_eq f (ha.trans y.2.symm), zero_mul]
end BSLambda
end
end

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) (v : Input V → ℝ) (x : Ones f) :
    (adj f *ᵥ v) x.1 = (biadj f *ᵥ fun z : Zeros f ↦ v z.1) x := by
  change ∑ y : Input V, adj f x.1 y * v y = ∑ z : Zeros f, biadj f x z * v z.1
  rw [← sum_ones_add_sum_zeros f fun y ↦ adj f x.1 y * v y,
    sum_adj_mul_eq_zero_of_apply_eq f v x.2, zero_add]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  rw [biadj_eq_adj]
end BSLambda
