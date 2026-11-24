-- Prove2me | solution 1 for BSLambda.adj_comp_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:52.208984+00:00
-- url     : https://prove2.me/submissions/ac679b86-d966-4bac-9b24-68b5141f2c94

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_comp_apply_topBits
public import Theorems.Thm_BSLambda_flipSet_prod_singleton
public import Theorems.Thm_BSLambda_topBits_setBlk_of_eq
public import Theorems.Thm_BSLambda_topBits_setBlk_of_ne
public import Theorems.Thm_BSLambda_adj_apply_eq_one_iff
public import Theorems.Thm_BSLambda_adj_eq_zero_of_apply_eq
public import Theorems.Thm_BSLambda_hammingDist_flipSet_singleton


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool) (x : Input (W × V)) (w : W)
    (v : V) :
    adj (comp f g) x (flipSet x {(w, v)})
      = adj f (topBits g x) (flipSet (topBits g x) {w})
        * adj g (blk x w) (flipSet (blk x w) {v}) := by
  by_cases hg : g (flipSet (blk x w) {v}) = g (blk x w)
  · -- The flip is invisible to `g`, hence to `comp f g`: both sides vanish.
    have h1 : topBits g (flipSet x {(w, v)}) = topBits g x :=
      (flipSet_prod_singleton x w v) ▸ topBits_setBlk_of_eq g x w _ hg
    rw [adj_eq_zero_of_apply_eq g hg.symm, mul_zero]
    exact adj_eq_zero_of_apply_eq (comp f g) (congrArg f h1.symm)
  · -- The flip changes the `w`-th top bit, so the two edges match up.
    have h1 : topBits g (flipSet x {(w, v)}) = flipSet (topBits g x) {w} :=
      (flipSet_prod_singleton x w v) ▸ topBits_setBlk_of_ne g x w _ hg
    have h2 : adj g (blk x w) (flipSet (blk x w) {v}) = 1 :=
      adj_apply_eq_one_iff.2 ⟨hammingDist_flipSet_singleton _ _, fun hne ↦ hg hne.symm⟩
    rw [h2, mul_one, adj_apply, adj_apply, comp_apply_topBits, comp_apply_topBits, h1,
      hammingDist_flipSet_singleton, hammingDist_flipSet_singleton]
end BSLambda
