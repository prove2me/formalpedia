-- Prove2me | solution 1 for Formalism.MainNotions.G.ValuationFitting.Em_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:40:09.68283+00:00
-- url     : https://prove2.me/submissions/ac86d199-6fd3-4c79-a05d-302c3caaade0

import Definitions.Def_ReciprocityTheory_DualLattices_MatEquivApply
import Definitions.Def_ReciprocityTheory_DualLattices_BlockOneMulMulBlockOne
import Definitions.Def_ReciprocityTheory_DualLattices_ProdDvdOfIso
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenCokerDet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_FittingIdeal_DetMulMemFitt0
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt



set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.ValuationFitting
open ReciprocityTheory.PGsh.Up
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.G.ValuationFitting
theorem _root_.solution {m h : ℕ} (w : Fin h → R) (j : Fin m) :
    (Em R m h *ᵥ w) j = if hj : (j : ℕ) < h then w ⟨j, hj⟩ else 0 := by
  simp only [Matrix.mulVec, dotProduct, Em, Matrix.of_apply]
  split_ifs with hj
  · rw [Finset.sum_eq_single ⟨j, hj⟩]
    · simp
    · intro b _ hb
      rw [if_neg (fun e => hb (Fin.ext e)), zero_mul]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · apply Finset.sum_eq_zero
    intro b _
    have := b.isLt
    rw [if_neg (by omega), zero_mul]
end Formalism.MainNotions.G.ValuationFitting
