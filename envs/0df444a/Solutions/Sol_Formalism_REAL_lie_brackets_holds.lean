-- Prove2me | solution 1 for Formalism.REAL.lie_brackets_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:21:22.552568+00:00
-- url     : https://prove2.me/submissions/8d7e6089-d85b-4f15-9155-a44306d37190

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_theta_theta
import Theorems.Thm_Formalism_REAL_f1alg_comm_iff
import Theorems.Thm_Formalism_REAL_f1alg_anti_iff
import Theorems.Thm_Formalism_REAL_f1alg_inG_iff
import Theorems.Thm_Formalism_REAL_f1alg_inK_iff
import Theorems.Thm_Formalism_REAL_mem_cartanP_iff
import Theorems.Thm_Formalism_REAL_f1alg_ct_theta
import Theorems.Thm_Formalism_REAL_f1alg_theta_comm
import Theorems.Thm_Formalism_REAL_f1alg_ct_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : Brackets := by
  intro n ε X Y

  have hK : ∀ Z, inK ε Z ↔ Zᴴ = -Z ∧ Jm ε * Z * Jm ε = Z := fun Z => by
    rw [f1alg_inK_iff, f1alg_comm_iff]
  have hP : ∀ Z, inP ε Z ↔ Zᴴ = Z ∧ Jm ε * Z * Jm ε = -Z := fun Z => by
    rw [mem_cartanP_iff, f1alg_anti_iff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hx hy
    rw [hK] at hx hy ⊢
    exact ⟨by rw [f1alg_ct_comm, hx.1, hy.1]; noncomm_ring, by rw [f1alg_theta_comm, hx.2, hy.2]⟩
  · intro hx hy
    rw [hK] at hx
    rw [hP] at hy ⊢
    exact ⟨by rw [f1alg_ct_comm, hx.1, hy.1]; noncomm_ring,
      by rw [f1alg_theta_comm, hx.2, hy.2]; noncomm_ring⟩
  · intro hx hy
    rw [hP] at hx hy
    rw [hK]
    exact ⟨by rw [f1alg_ct_comm, hx.1, hy.1]; noncomm_ring,
      by rw [f1alg_theta_comm, hx.2, hy.2]; noncomm_ring⟩
  · intro hX
    have hx := (f1alg_inG_iff ε X).mp hX
    have htt := f1alg_theta_theta ε X
    have hct := f1alg_ct_theta ε X
    have h2 : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by simp
    refine ⟨(2 : ℂ)⁻¹ • (X + Jm ε * X * Jm ε), (2 : ℂ)⁻¹ • (X - Jm ε * X * Jm ε), ?_, ?_, ?_⟩
    · rw [hK]
      constructor
      · rw [conjTranspose_smul, conjTranspose_add, hct, hx, h2, Matrix.mul_neg, Matrix.neg_mul, htt]
        module
      · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, htt]
        module
    · rw [hP]
      constructor
      · rw [conjTranspose_smul, conjTranspose_sub, hct, hx, h2, Matrix.mul_neg, Matrix.neg_mul, htt]
        module
      · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, htt]
        module
    · module
  · intro hx hy
    rw [hK] at hx
    rw [hP] at hy
    have h : X = -X := hy.1.symm.trans hx.1
    ext i j
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.neg_apply] at hij
    rw [Matrix.zero_apply]
    linear_combination hij / 2
end Formalism.REAL
