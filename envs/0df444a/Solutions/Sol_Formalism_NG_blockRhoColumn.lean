-- Prove2me | solution 1 for Formalism.NG.blockRhoColumn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:08:19.82099+00:00
-- url     : https://prove2.me/submissions/f338f512-d96a-476f-8b94-7ba8e70d2cb3

import Definitions.Def_Formalism_CharacterColumnKernels_StatementColKer
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKer
import Theorems.Thm_Formalism_NG_colKer
import Theorems.Thm_Formalism_NG_blockRhoAbs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
open ColumnGeneratorDecomposition
namespace Formalism.NG
theorem _root_.solution : StatBlockRhoColumn := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0 ℓ
    hE hk0 hδ heq hlift ρM Ψ hΨ hcob what₂ F lenRow Q s cols eO vδ N h0 hrows hcols hQ hsel
  have hk := colKer O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
    Kc k0 ℓ (fun l => e' (colIdx l)) hE hk0 hδ heq hlift
  rw [← hΨ] at hk
  refine blockRhoAbs O G d ρM _ Ψ δO hcob ι' what₂ cols D F lenRow Q s ℓ e' j h0 hrows hcols hQ
    hsel (le_of_le_of_eq hk ?_)
  simp only [cols, h0]
  rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy), Finset.card_image_of_injective _ hinj,
    Finset.card_univ]
end Formalism.NG
