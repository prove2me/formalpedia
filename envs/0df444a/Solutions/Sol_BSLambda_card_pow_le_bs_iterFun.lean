-- Prove2me | solution 1 for BSLambda.card_pow_le_bs_iterFun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:37:50.546825+00:00
-- url     : https://prove2.me/submissions/d4ecabf3-8326-4dc7-b6c8-7191a32117c4

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Theorems.Thm_BSLambda_card_iterCoord
public import Theorems.Thm_BSLambda_iterFun_zeroInput
public import Theorems.Thm_BSLambda_iterFun_flipSet_iterBlock
public import Theorems.Thm_BSLambda_iterBlock_nonempty
public import Theorems.Thm_BSLambda_iterBlock_disjoint
public import Theorems.Thm_BSLambda_card_le_bs_of_blocks
public import Theorems.Thm_BSLambda_isSensitiveBlock_of_eq_true


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open Function
universe u
namespace BSLambda
theorem _root_.solution {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    {f : Input V → Bool} {blk : ι → Finset V}
    (hzero : f (zeroInput V) = false)
    (hflip : ∀ i, f (flipSet (zeroInput V) (blk i)) = true)
    (hne : ∀ i, (blk i).Nonempty)
    (hdisj : Pairwise (Disjoint on blk)) (m : ℕ) :
    Fintype.card ι ^ m ≤ bs (iterFun f m) := by
  have h := card_le_bs_of_blocks (s := (Finset.univ : Finset (IterCoord ι m)))
    (fun t _ ↦ isSensitiveBlock_of_eq_true (iterBlock_nonempty hne m t)
      (iterFun_zeroInput hzero m) (iterFun_flipSet_iterBlock hzero hflip m t))
    fun t _ u _ htu ↦ iterBlock_disjoint hdisj m htu
  rwa [Finset.card_univ, card_iterCoord] at h
end BSLambda
