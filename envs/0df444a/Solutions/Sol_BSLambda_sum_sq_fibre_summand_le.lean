-- Prove2me | solution 1 for BSLambda.sum_sq_fibre_summand_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:41:44.916907+00:00
-- url     : https://prove2.me/submissions/a87253b0-88ca-49d5-925a-324dc7c4c773

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_sum_sq_block_le

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (b : Input W) (w : W) :
    ∑ x : Input (W × V), (if topBits g x = b then
        adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
      ≤ (adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w}))) ^ 2 := by
  have hfactor (x : Input (W × V)) :
      (if topBits g x = b then
          adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
        = adj f b (flipSet b {w}) ^ 2
          * (if topBits g x = b then (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2 := by
    split <;> ring
  rw [Finset.sum_congr rfl fun x _ ↦ hfactor x, ← Finset.mul_sum, mul_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (sum_sq_block_le g ψ b w) (sq_nonneg _)
end BSLambda
