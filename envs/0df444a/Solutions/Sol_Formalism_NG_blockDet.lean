-- Prove2me | solution 1 for Formalism.NG.blockDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:17:34.01172+00:00
-- url     : https://prove2.me/submissions/880c8f5a-a059-4239-809d-20809f0f481f

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
import Theorems.Thm_Formalism_NG_BlockDetAlt_mem_Fr
import Theorems.Thm_Formalism_NG_BlockDetAlt_schur
import Theorems.Thm_Formalism_NG_BlockDetAlt_phiMat_good
import Theorems.Thm_Formalism_NG_BlockDetAlt_phiMat_const
import Theorems.Thm_Formalism_NG_BlockDetAlt_phiMat_eval

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
open BlockDetAlt
namespace Formalism.NG
theorem _root_.solution : StatBlockDet := by
  intro O _ _ X' T' d _ _ R' hyp g _ _ Θ
  have hS := schur T' R' hyp g (phiMat R' Θ) (fun p q => phiMat_good R' Θ p q) (phiMat_const R' Θ)
  obtain ⟨f, hf, hfx⟩ := mem_Fr.1 (hS (Fintype.card (g × d)))
  refine ⟨(-1) ^ Fintype.card (g × d) * f, T'.mul_mem (T'.pow_mem (T'.neg_mem T'.one_mem) _) hf, fun x' => ?_⟩
  rw [phiMat_eval R' Θ x', ← hfx x']
  simp
end Formalism.NG
