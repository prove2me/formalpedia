-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.section_at_block_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:58:17.791969+00:00
-- url     : https://prove2.me/submissions/4fe014b2-cba0-438c-b4f0-6a3ed64b7a40

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_blk_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_blk_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_exists_blk_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_exists_blk_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lower_mul_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_coordU
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upper_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_block_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_mul_diag_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_mul_diag_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_stabilizer_block_point

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open G4
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.SectionBlock := by
  intro n t c ht l u hl hu
  obtain ⟨l', α, hl', rfl⟩ := exists_blk_lower hl
  obtain ⟨u', β, hu', rfl⟩ := exists_blk_upper hu
  have hk0 := upperUni_conj hl'
  refine ⟨(α ᵥ* l'⁻¹, coordU (wMat n * l' * wMat n * u'), (wMat n * l' * wMat n) *ᵥ β),
    ⟨blk l'⁻¹ 0 0 1, blk (wMat n * l' * wMat n) 0 0 1, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (lowerUni_blk_iff _ _ _ _).2 ⟨lowerUni_inv hl', rfl, rfl⟩
  · exact (upperUni_blk_iff _ _ _ _).2 ⟨hk0, rfl, rfl⟩
  · rw [block_prod]
    unfold ptBlock
    rw [blk_inj]
    exact ⟨(stab_smul ht _ _).2 (stab_exists hl'), by simp, by simp, by simp⟩
  · rw [blk_mul_diag_right, lower_mul_inv hl']
    rfl
  · rw [blk_mul_diag_left]
    dsimp only
    rw [upper_coordU (upperUni_mul hk0 hu')]
  · rintro ⟨a, v, b⟩ ⟨k, k', hk, hk', h3, h4, h5⟩
    obtain ⟨κ, hκ, rfl, rfl⟩ := ((stabilizer_block_point n t c ht k k' hk hk').1).1 h3
    dsimp only at h4 h5
    unfold lowRow at h4
    rw [blk_mul_diag_right, blk_inj] at h4
    rw [blk_mul_diag_left, blk_inj] at h5
    obtain ⟨h41, _, h43, _⟩ := h4
    obtain ⟨h51, h52, _, _⟩ := h5
    have hκ0 : κ = wMat n * l' * wMat n := stab_right h41 ((stab_core hκ).2 rfl)
    have hinv : l'⁻¹ = wMat n * κ⁻¹ * wMat n := Matrix.inv_eq_right_inv h41
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · show a = α ᵥ* l'⁻¹
      rw [hinv, h43]
    · show v = coordU (wMat n * l' * wMat n * u')
      apply upper_injective
      rw [upper_coordU (upperUni_mul hk0 hu'), ← h51, hκ0]
    · show b = (wMat n * l' * wMat n) *ᵥ β
      rw [← h52, hκ0]
end Formalism.FourierDecayAlt.P
