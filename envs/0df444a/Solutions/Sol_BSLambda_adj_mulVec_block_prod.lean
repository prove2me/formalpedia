-- Prove2me | solution 1 for BSLambda.adj_mulVec_block_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:38:26.514274+00:00
-- url     : https://prove2.me/submissions/dca67c8b-4bd1-4714-9da4-2977d5171bc6

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_prod_blk_setBlk
public import Theorems.Thm_BSLambda_topBits_setBlk_of_ne
public import Theorems.Thm_BSLambda_apply_ne_of_adj_ne_zero


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (g : Input V → Bool) {u : Input V → ℝ} (v : Input W → ℝ)
    (hu : adj g *ᵥ u = lam g • u) (x : Input (W × V)) (w : W) :
    (adj g *ᵥ fun z : Input V ↦
        v (topBits g (setBlk x w z)) * ∏ w' : W, u (blk (setBlk x w z) w')) (blk x w)
      = lam g * v (flipSet (topBits g x) {w}) * ∏ w' : W, u (blk x w') := by
  have hstep : (adj g *ᵥ fun z : Input V ↦
        v (topBits g (setBlk x w z)) * ∏ w' : W, u (blk (setBlk x w z) w')) (blk x w)
      = ∑ z : Input V, adj g (blk x w) z
          * (v (flipSet (topBits g x) {w})
            * (u z * ∏ w' ∈ Finset.univ.erase w, u (blk x w'))) := by
    change ∑ z : Input V, adj g (blk x w) z
        * (v (topBits g (setBlk x w z)) * ∏ w' : W, u (blk (setBlk x w z) w')) = _
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases hz : adj g (blk x w) z = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [topBits_setBlk_of_ne g x w z (apply_ne_of_adj_ne_zero g hz).symm,
        prod_blk_setBlk u x w z]
  have hpull : ∑ z : Input V, adj g (blk x w) z
        * (v (flipSet (topBits g x) {w})
          * (u z * ∏ w' ∈ Finset.univ.erase w, u (blk x w')))
      = (v (flipSet (topBits g x) {w}) * ∏ w' ∈ Finset.univ.erase w, u (blk x w'))
        * ∑ z : Input V, adj g (blk x w) z * u z := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun z _ ↦ by ring
  have hev : ∑ z : Input V, adj g (blk x w) z * u z = lam g * u (blk x w) :=
    congrFun hu (blk x w)
  rw [hstep, hpull, hev,
    ← Finset.mul_prod_erase Finset.univ (fun w' ↦ u (blk x w')) (Finset.mem_univ w)]
  ring
end BSLambda
