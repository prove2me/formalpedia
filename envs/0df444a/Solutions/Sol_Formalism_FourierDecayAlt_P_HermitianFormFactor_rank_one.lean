-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.rank_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:43:45.052653+00:00
-- url     : https://prove2.me/submissions/79d3c2a5-bd08-4479-aca0-eea8254da5bc

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_lin_subst
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_gram_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_meas_gram
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_rank_one_std
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_rmulL
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_rmulL_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution (G₀ : (Q → Q → ℂ) → ℝ≥0∞) (hG : Measurable G₀) (h0 : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₀ T = 0)
    (b : Q → ℂ) :
    ∫⁻ X : Q → Q → ℂ, G₀ (gram X - Matrix.vecMulVec (star b) b) = ∫⁻ X : Q → Q → ℂ, G₀ (gram X) := by
  by_cases hb : b = 0
  · subst hb; simp
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.1 hb
  have hj₀' : b j₀ ≠ 0 := hj₀
  set A : Matrix Q Q ℂ := ((1 : Matrix Q Q ℂ).updateCol j₀ b)ᵀ with hA
  have hdet : A.det = b j₀ := by
    rw [hA, Matrix.det_transpose, ← Matrix.cramer_apply, Matrix.cramer_one]; rfl
  have hU : IsUnit A.det := by rw [hdet]; exact isUnit_iff_ne_zero.2 hj₀'
  have hAU : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 hU
  have hrow : ∀ l, A j₀ l = b l := by
    intro l; simp [hA, Matrix.transpose_apply]
  have hE : Aᴴ * Matrix.single j₀ j₀ (1 : ℂ) * A = Matrix.vecMulVec (star b) b := by
    ext i l
    rw [Matrix.mul_apply, Finset.sum_eq_single j₀]
    · rw [Matrix.mul_apply, Finset.sum_eq_single j₀]
      · simp [hrow, Matrix.vecMulVec_apply]
      · intro x _ hx
        simp [Ne.symm hx]
      · simp
    · intro x _ hx
      have : (Aᴴ * Matrix.single j₀ j₀ (1 : ℂ)) i x = 0 := by
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun y _ => ?_
        simp [Ne.symm hx]
      rw [this, zero_mul]
    · simp
  have : (volume : Measure (Q → Q → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure (fun _ : Q => (volume : Measure (Q → ℂ)))
  obtain ⟨c, hc⟩ := lin_subst (volume : Measure (Q → Q → ℂ)) _ _ (rmulL_comp A A⁻¹ (Matrix.nonsing_inv_mul A hU))
  refine (hc (fun X => G₀ (gram X - Matrix.vecMulVec (star b) b)) (meas_gram_sub G₀ hG _)).trans
    (Eq.trans ?_ (hc (fun X => G₀ (gram X)) (meas_gram G₀ hG)).symm)
  congr 1
  let G₁ : (Q → Q → ℂ) → ℝ≥0∞ := fun T => G₀ (Aᴴ * (Matrix.of T) * A)
  have hG₁ : Measurable G₁ := by
    refine hG.comp (Continuous.measurable ?_)
    exact ((continuous_const (y := Aᴴ)).matrix_mul (continuous_id (X := Matrix Q Q ℂ))).matrix_mul continuous_const
  have h0₁ : ∀ T : Matrix Q Q ℂ, ¬ T.PosDef → G₁ T = 0 := by
    intro T hT
    refine h0 _ fun hP => hT ?_
    exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hAU).1 hP
  have := rank_one_std G₁ hG₁ h0₁ j₀
  have e1 : ∀ X : Q → Q → ℂ, G₀ (gram (rmulL A X) - Matrix.vecMulVec (star b) b) = G₁ (gram X - Matrix.single j₀ j₀ (1 : ℂ)) := by
    intro X
    show _ = G₀ (Aᴴ * (gram X - Matrix.single j₀ j₀ (1 : ℂ)) * A)
    rw [gram_rmulL, Matrix.mul_sub, Matrix.sub_mul, hE]
  have e2 : ∀ X : Q → Q → ℂ, G₀ (gram (rmulL A X)) = G₁ (gram X) := by
    intro X
    show _ = G₀ (Aᴴ * gram X * A)
    rw [gram_rmulL]
  simp_rw [e1, e2]
  exact this
end Formalism.FourierDecayAlt.P.HermitianFormFactor
