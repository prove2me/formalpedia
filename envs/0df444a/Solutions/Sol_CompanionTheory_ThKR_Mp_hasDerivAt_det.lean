-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.hasDerivAt_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:31:34.433746+00:00
-- url     : https://prove2.me/submissions/67e6f2f4-2e09-48ba-b95a-6beb9644c341

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_hasDerivAt
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul


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
theorem _root_.solution (P K : Matrix l l ℂ) (t₀ : ℝ) (hP : (P + (t₀ : ℂ) • K).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (P + (t : ℂ) • K).det)
      ((P + (t₀ : ℂ) • K).det * ((P + (t₀ : ℂ) • K)⁻¹ * K).trace) t₀ := by
  have hu : IsUnit (P + (t₀ : ℂ) • K).det := hP.isUnit
  have e : ∀ t : ℝ, (P + (t : ℂ) • K).det = (P + (t₀ : ℂ) • K).det *
      (1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * ((t - t₀ : ℝ) : ℂ) +
        (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval
          ((t - t₀ : ℝ) : ℂ) * ((t - t₀ : ℝ) : ℂ) ^ 2) := fun t => by
    rw [← Matrix.det_one_add_smul, ← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ofReal_sub, sub_smul]
    congr 1
    abel
  have hφ : HasDerivAt (fun z : ℂ => 1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * z +
      (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval z * z ^ 2)
      ((P + (t₀ : ℂ) • K)⁻¹ * K).trace ((t₀ - t₀ : ℝ) : ℂ) := by
    have := (((hasDerivAt_id (0 : ℂ)).const_mul ((P + (t₀ : ℂ) • K)⁻¹ * K).trace).const_add 1).add
      ((Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial ℂ) •
        ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
    rw [sub_self, ofReal_zero]
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq (.of_forall fun z => by simp)
  have hh : HasDerivAt (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) 1 t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).ofReal_comp
  have := (hφ.comp t₀ hh).const_mul (P + (t₀ : ℂ) • K).det
  rw [mul_one] at this
  exact this.congr_of_eventuallyEq (.of_forall e)
end CompanionTheory.ThKR.Mp
