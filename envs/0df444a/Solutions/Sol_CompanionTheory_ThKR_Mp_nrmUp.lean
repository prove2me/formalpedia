-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.nrmUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:56:50.766355+00:00
-- url     : https://prove2.me/submissions/86005c95-1faf-4600-aad9-4a0b9528576b

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_ddNe
import Theorems.Thm_CompanionTheory_ThKR_Mp_nn_mem
import Theorems.Thm_CompanionTheory_ThKR_Mp_upperPart_unipotent_mul
import Theorems.Thm_CompanionTheory_ThKR_Mp_loQ_nn
import Theorems.Thm_CompanionTheory_ThKR_Mp_UU_dRho
import Theorems.Thm_CompanionTheory_ThKR_Mp_UU_zero
import Theorems.Thm_CompanionTheory_ThKR_Mp_hasDerivAt_UU
import Theorems.Thm_CompanionTheory_ThKR_Mp_hess
import Theorems.Thm_CompanionTheory_ThKR_Mp_trace_eq
import Theorems.Thm_CompanionTheory_ThKR_Mp_hasDerivAt_det
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_differentiableAt
import Theorems.Thm_CompanionTheory_ThKR_LL_fou_mq_fouInv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution : NrmUp l := by
  intro S hS s' f hf
  have hPt : ∀ t : ℝ, upperParabolic (nn S t * s'.1) = upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1) := fun t => upperPart_unipotent_mul S t s'.1
  have hdet : ∀ t : ℝ, (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det ≠ 0 := fun t => by
    rw [← hPt]
    exact ddNe ⟨_, mul_mem (nn_mem hS t) s'.2⟩
  have hAnn : ∀ t, Ann (nn S t * s'.1) (UU S t f) := fun t => hf.map (UU_dRho hS t)
  have hF : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0) (-(1 / 2 : ℂ) * UU S t f 0 *
      ((upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1))⁻¹ * (S.map ofReal * loQ s'.1)).trace) t := fun t => by
    have h1 := hasDerivAt_UU S f t
    rw [fou_mq_fouInv] at h1
    simp only [SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul] at h1
    have h2 := trace_eq (hdet t) (S.map ofReal)
      (Matrix.of fun a k => (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)}
        (UU S t f))) 0) (-(2 * π * I) * UU S t f 0) (fun j k => by
          have := hess (hAnn t) j k
          rw [hPt, loQ_nn] at this
          simp only [Matrix.of_apply]
          rw [this]
          ring)
    simp only [Matrix.of_apply, Matrix.map_apply] at h2
    rw [h2] at h1
    convert h1 using 1
    have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    ring
  have hh : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0 * UU S t f 0 *
      (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det) 0 t := fun t => by
    exact (((hF t).fun_mul (hF t)).fun_mul (hasDerivAt_det _ _ t (hdet t))).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hh t).differentiableAt) (fun t => (hh t).deriv) 1 0
  have e0 : UU S 0 f = f := by rw [UU_zero]; rfl
  have e1 : UU S 1 f = fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f)) := by
    simp [UU]
  simp only [e0, e1, ofReal_zero, ofReal_one, zero_smul, add_zero, one_smul] at hc
  rw [sq, sq]
  exact hc
end CompanionTheory.ThKR.Mp
