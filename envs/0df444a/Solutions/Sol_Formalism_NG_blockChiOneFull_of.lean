-- Prove2me | solution 1 for Formalism.NG.blockChiOneFull_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:24:37.840698+00:00
-- url     : https://prove2.me/submissions/4841685b-cc6d-4509-a820-fdc0ada09722

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Theorems.Thm_Formalism_NG_IdempotentColumnIndexImages_sum_image_colIdx
import Theorems.Thm_Formalism_NG_IdempotentColumnIndexImages_card_image_colIdx
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_final_arith
import Theorems.Thm_Formalism_NG_TrivialCharacterBlockLength_blockTrivAbs
import Theorems.Thm_Formalism_NG_TrivialCharacterBlockLength_final_arith
import Theorems.Thm_Formalism_NG_colPsiKer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
universe u₁ u₂ u₃ u₄ u₅ u₆
namespace Formalism.NG
theorem _root_.solution (hK : StatColKerChiOne.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiOneFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0 ℓ cB
    hd hu he₁ hEM hδ hk0 ρM Ψ lrows qs F deg vζ Q vhE cols eO vδ hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hB : ∀ x ∈ coB1 ρM, x = 0 := by
    rintro _ ⟨v, rfl⟩
    funext g
    exact (show uElt r χ g • v - v = 0 by rw [hu, sub_self])
  have h := TrivialCharacterBlockLength.blockTrivAbs ρM hB Ψ (lrows ∪ qs) cols D F lenRow Q vhE hrows hcols hQ hsel
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    ℓ (fun l => e' (colIdx l)) hu he₁ hEM (fun m => by rw [algebraMap_smul]; exact hδ m) hk0
  have hker : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) + (cols.card : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans (le_of_eq ?_)
    rw [hd, Nat.cast_one, mul_one, IdempotentColumnIndexImages.card_image_colIdx colIdx hinj,
      IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun w => eO * (e' w : ℕ∞) + 2 * vδ)]
    simp only [one_mul]
    rfl
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  rw [hsum] at h
  exact h.trans (TrivialCharacterBlockLength.final_arith _ _ _ _ _ _ _ hker)
end Formalism.NG
