-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.hasDerivAt_UU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:28:47.056291+00:00
-- url     : https://prove2.me/submissions/8a05635b-f112-4687-a1b4-8edb97f0b4ef

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_fou_zero
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_continuous
import Theorems.Thm_CompanionTheory_ThKR_LL_fouInv_mul_fou
import Theorems.Thm_CompanionTheory_ThKR_LL_mq_apply
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_apply


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
theorem _root_.solution (S : Matrix l l ℝ) (f : Sch l) (t₀ : ℝ) :
    HasDerivAt (fun t => UU S t f 0)
      (fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l (UU S t₀ f))) 0) t₀ := by
  have e1 : ∀ t, UU S t f 0 = ∫ x, ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x := fun t => by
    rw [UU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, fou_zero]
  have e2 : fouInv l (UU S t₀ f) = ph (-(t₀ • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) := by
    rw [UU, ← ContinuousLinearMap.mul_apply, ← mul_assoc, fouInv_mul_fou, one_mul, ContinuousLinearMap.mul_apply]
  have hq : ∀ x : Eu l, |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2 := fun x =>
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x‖
          ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖) := by
            gcongr
            exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S).le_opNorm x
        _ = _ := by ring)
  have ph_eq : ∀ (t : ℝ) (x : Eu l), ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x =
      exp (((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ) * I) * fouInv l f x := fun t x => by
    have : -π * ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t := by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right,
        real_inner_smul_right]
      ring
    rw [ph_apply, this]
  have mq_eq : ∀ (h : Sch l) (x : Eu l), mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) h x =
      ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) * I * h x := fun h x => by
    have : -π * ⟪x, (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ := by
      simp only [ContinuousLinearMap.neg_apply, inner_neg_right]
      ring
    rw [mq_apply, this]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun t x => ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x)
    (F' := fun t x => mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S))
      (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f)) x)
    (bound := fun x => π * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * (‖x‖ ^ 2 * ‖fouInv l f x‖))
    Filter.univ_mem (.of_forall fun t => (ph _ (fouInv l f)).continuous.aestronglyMeasurable)
    ((ph _ (fouInv l f)).integrable) ((mq _ _).continuous.aestronglyMeasurable)
    (.of_forall fun x t _ => by
      rw [mq_eq, ph_eq, norm_mul, norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
      have h1 := hq x
      have h2 := norm_nonneg (fouInv l f x)
      calc π * |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * 1 * (1 * ‖fouInv l f x‖)
          = π * (|⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * ‖fouInv l f x‖) := by ring
        _ ≤ π * ((‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2) * ‖fouInv l f x‖) := by gcongr
        _ = _ := by ring)
    (((fouInv l f).integrable_pow_mul volume 2).const_mul _)
    (.of_forall fun x t _ => by
      simp only [ph_eq, mq_eq]
      have h1 : HasDerivAt (fun t : ℝ => ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ))
          ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).const_mul (π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫)).ofReal_comp
        simpa using this
      exact ((h1.mul_const I).cexp.mul_const (fouInv l f x)).congr_deriv (by ring))
  rw [e2, fou_zero]
  exact key.2.congr_of_eventuallyEq (.of_forall e1)
end CompanionTheory.ThKR.Mp
