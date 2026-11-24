-- Prove2me | solution 1 for BSLambda.sum_sq_block_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:59.451804+00:00
-- url     : https://prove2.me/submissions/778679c3-1f38-418e-984a-dcd05450e249

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_topBits_setBlk_ne
public import Theorems.Thm_BSLambda_topBits_setBlk_eq_iff
public import Theorems.Thm_BSLambda_sq_fibreNorm
public import Theorems.Thm_BSLambda_sum_setBlk
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
public import Theorems.Thm_BSLambda_sum_sq_adj_mulVec_side_le
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
theorem _root_.solution (g : Input V → Bool) (ψ : Input (W × V) → ℝ) (b : Input W) (w : W) :
    ∑ x : Input (W × V),
        (if topBits g x = b then (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0) ^ 2
      ≤ lam g ^ 2 * fibreNorm g ψ (flipSet b {w}) ^ 2 := by
  have hflip : ∀ w' : W, w' ≠ w → flipSet b {w} w' = b w' :=
    fun w' hw' ↦ flipSet_apply_of_notMem (Finset.notMem_singleton.mpr hw')
  rw [sq_fibreNorm, ← sum_setBlk w, ← sum_setBlk w, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  by_cases hP : ∀ w' : W, w' ≠ w → topBits g y.1 w' = b w'
  · -- Off `w` the input `setBlk y.1 w a` already agrees with `b`, so lying in the fibre over
    -- any such `c` is a condition on the single bit `g a`.
    have hL : ∀ a : Input V, (topBits g (setBlk y.1 w a) = b) ↔ (g a = b w) :=
      topBits_setBlk_eq_iff g y.1 w hP
    have hR (a : Input V) : (topBits g (setBlk y.1 w a) = flipSet b {w}) ↔ ¬ (g a = b w) := by
      rw [topBits_setBlk_eq_iff g y.1 w (fun w' hw' ↦ (hP w' hw').trans (hflip w' hw').symm) a,
        flipSet_apply_of_mem (Finset.mem_singleton_self w)]
      cases b w <;> simp
    have hLsum (a : Input V) :
        (if topBits g (setBlk y.1 w a) = b then
            (adj g *ᵥ fun z ↦ ψ (setBlk (setBlk y.1 w a) w z)) (blk (setBlk y.1 w a) w)
          else 0) ^ 2
          = (if g a = b w then (adj g *ᵥ fun z ↦ ψ (setBlk y.1 w z)) a else 0) ^ 2 := by
      simp only [setBlk_setBlk, blk_setBlk, Function.update_self]
      by_cases hga : g a = b w
      · rw [if_pos ((hL a).2 hga), if_pos hga]
      · rw [if_neg fun h ↦ hga ((hL a).1 h), if_neg hga]
    have hRsum (a : Input V) :
        (if topBits g (setBlk y.1 w a) = flipSet b {w} then ψ (setBlk y.1 w a) else 0) ^ 2
          = (if g a = b w then 0 else ψ (setBlk y.1 w a)) ^ 2 := by
      by_cases hga : g a = b w
      · rw [if_neg fun h ↦ (hR a).1 h hga, if_pos hga]
      · rw [if_pos ((hR a).2 hga), if_neg hga]
    rw [Finset.sum_congr rfl fun a _ ↦ hLsum a, Finset.sum_congr rfl fun a _ ↦ hRsum a]
    exact sum_sq_adj_mulVec_side_le g (fun z ↦ ψ (setBlk y.1 w z)) (b w)
  · -- Off `w` the input `setBlk y.1 w a` disagrees with `b`, so both sides vanish.
    push Not at hP
    obtain ⟨w', hw'ne, hw'⟩ := hP
    have hw'flip : topBits g y.1 w' ≠ flipSet b {w} w' := by
      rw [hflip w' hw'ne]
      exact hw'
    simp [topBits_setBlk_ne g y.1 w hw'ne hw', topBits_setBlk_ne g y.1 w hw'ne hw'flip]
end BSLambda
