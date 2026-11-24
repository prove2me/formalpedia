-- Prove2me | solution 1 for BSLambda.sum_sq_fibre_adj_comp_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:42:32.805284+00:00
-- url     : https://prove2.me/submissions/149cf038-a3e0-40be-a737-f16735ba0714

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_sum_sq_sum_le_sq_sum
public import Theorems.Thm_BSLambda_adj_comp_mulVec_apply
public import Theorems.Thm_BSLambda_fibreNorm_nonneg
public import Theorems.Thm_BSLambda_sum_sq_fibre_summand_le
public import Theorems.Thm_BSLambda_adj_mulVec_apply
public import Theorems.Thm_BSLambda_adj_nonneg
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
public import Theorems.Thm_BSLambda_lam_nonneg
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
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool)
    (ψ : Input (W × V) → ℝ) (b : Input W) :
    ∑ x : Input (W × V), (if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0) ^ 2
      ≤ lam g ^ 2 * ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 := by
  have hmaster (x : Input (W × V)) : ∑ w : W, (if topBits g x = b then
      adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0)
        = if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0 := by
    by_cases hx : topBits g x = b
    · subst hx
      simp only [reduceIte]
      exact (adj_comp_mulVec_apply f g ψ x).symm
    · simp [hx]
  have ht0 (w : W) : 0 ≤ adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w})) :=
    mul_nonneg (adj_nonneg f _ _) (mul_nonneg (lam_nonneg g) (fibreNorm_nonneg g ψ _))
  have htsum : ∑ w : W, adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w}))
      = lam g * (adj f *ᵥ fibreNorm g ψ) b := by
    rw [adj_mulVec_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ ↦ by ring
  calc ∑ x : Input (W × V), (if topBits g x = b then (adj (comp f g) *ᵥ ψ) x else 0) ^ 2
      = ∑ x : Input (W × V), (∑ w : W, (if topBits g x = b then
          adj f b (flipSet b {w}) * (adj g *ᵥ fun z ↦ ψ (setBlk x w z)) (blk x w) else 0)) ^ 2 :=
        Finset.sum_congr rfl fun x _ ↦ by rw [hmaster x]
    _ ≤ (∑ w : W, adj f b (flipSet b {w}) * (lam g * fibreNorm g ψ (flipSet b {w}))) ^ 2 :=
        sum_sq_sum_le_sq_sum _ _ ht0 (sum_sq_fibre_summand_le f g ψ b)
    _ = lam g ^ 2 * ((adj f *ᵥ fibreNorm g ψ) b) ^ 2 := by rw [htsum, mul_pow]
end BSLambda
