-- Prove2me | solution 1 for BSLambda.adj_comp_mulVec_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:39:57.455106+00:00
-- url     : https://prove2.me/submissions/45b42611-b5ba-4dbe-b55c-3e137eb7c9d7

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_adj_comp_mulVec_apply
public import Theorems.Thm_BSLambda_adj_mulVec_block_prod
public import Theorems.Thm_BSLambda_adj_mulVec_apply
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_iterBlock_zero
public import Theorems.Thm_BSLambda_iterFun_zero
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.iterBlock_zero
attribute [local simp] BSLambda.iterFun_zero
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool) {u : Input V → ℝ}
    {v : Input W → ℝ} (hu : adj g *ᵥ u = lam g • u) (hv : adj f *ᵥ v = lam f • v) :
    adj (comp f g) *ᵥ (fun x ↦ v (topBits g x) * ∏ w, u (blk x w))
      = (lam f * lam g) • fun x ↦ v (topBits g x) * ∏ w, u (blk x w) := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [adj_comp_mulVec_apply]
  have hfin : ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
        * (lam g * v (flipSet (topBits g x) {w}) * ∏ w' : W, u (blk x w'))
      = lam f * lam g * (v (topBits g x) * ∏ w' : W, u (blk x w')) := by
    have h1 : ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
          * (lam g * v (flipSet (topBits g x) {w}) * ∏ w' : W, u (blk x w'))
        = (lam g * ∏ w' : W, u (blk x w'))
          * ∑ w : W, adj f (topBits g x) (flipSet (topBits g x) {w})
            * v (flipSet (topBits g x) {w}) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ ↦ by ring
    have h2 : (adj f *ᵥ v) (topBits g x) = lam f * v (topBits g x) := congrFun hv (topBits g x)
    rw [h1, ← adj_mulVec_apply f v (topBits g x), h2]
    ring
  rw [← hfin]
  exact Finset.sum_congr rfl fun w _ ↦ by rw [adj_mulVec_block_prod g v hu x w]
end BSLambda
