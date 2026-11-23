-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.stabilizer_block_point
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:55.809832+00:00
-- url     : https://prove2.me/submissions/6950ab4c-2196-42b4-aabf-425bd1bcf768

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_blk_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_exists_blk_upper
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_exists_blk_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_upperUni_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_lowerUni_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_w_det_ne
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_stab_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_block_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_G4_char_blk

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
theorem _root_.solution : Formalism.FourierDecayAlt.G.StabBlock := by
  intro n t c ht l u hl hu
  have h1 : l * ptBlock n t c * u = ptBlock n t c ↔
      ∃ k : Matrix (Fin n) (Fin n) ℂ, IsUpperUni k ∧ u = blk k 0 0 1 ∧
        l = blk (wMat n * k⁻¹ * wMat n) 0 0 1 := by
    constructor
    · intro h
      obtain ⟨l', α, hl', rfl⟩ := exists_blk_lower hl
      obtain ⟨u', β, hu', rfl⟩ := exists_blk_upper hu
      rw [block_prod] at h
      unfold ptBlock at h
      rw [blk_inj] at h
      obtain ⟨e1, e2, e3, _⟩ := h
      have hw : (t • wMat n).det ≠ 0 := by
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ ht) (w_det_ne n)
      have hβ : β = 0 := by
        refine Matrix.eq_zero_of_mulVec_eq_zero ?_ e2
        rw [Matrix.det_mul, lowerUni_det hl', one_mul]
        exact hw
      have hα : α = 0 := by
        refine Matrix.eq_zero_of_vecMul_eq_zero ?_ e3
        rw [Matrix.det_mul, upperUni_det hu', mul_one]
        exact hw
      refine ⟨u', hu', by rw [hβ], ?_⟩
      rw [hα, (stab_core hu').1 ((stab_smul ht _ _).1 e1)]
    · rintro ⟨k, hk, rfl, rfl⟩
      rw [block_prod]
      unfold ptBlock
      rw [blk_inj]
      exact ⟨(stab_smul ht _ _).2 ((stab_core hk).2 rfl), by simp, by simp, by simp⟩
  refine ⟨h1, fun h => ?_⟩
  obtain ⟨k, hk, rfl, rfl⟩ := h1.1 h
  exact char_blk hk
end Formalism.FourierDecayAlt.P
