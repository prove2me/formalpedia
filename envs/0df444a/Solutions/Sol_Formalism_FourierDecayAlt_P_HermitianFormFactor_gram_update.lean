-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.gram_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:40:57.398586+00:00
-- url     : https://prove2.me/submissions/28aa25b7-c0f3-420a-b7bd-2eda457f6c39

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_dot_conj

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
theorem _root_.solution (X : Q → Q → ℂ) (j₀ : Q) (n x₀ : Q → ℂ) (hn1 : star n ⬝ᵥ n = 1)
    (hnX : ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0) (hx₀ : star n ⬝ᵥ x₀ = 0) (ζ : ℂ) :
    gram (Function.update X j₀ (x₀ + ζ • n)) =
      gram (Function.update X j₀ x₀) + (Complex.normSq ζ : ℂ) • Matrix.single j₀ j₀ (1 : ℂ) := by
  have hx₀' : star x₀ ⬝ᵥ n = 0 := by rw [dot_conj, hx₀, star_zero]
  have hnX' : ∀ j, j ≠ j₀ → star (X j) ⬝ᵥ n = 0 := fun j hj => by rw [dot_conj, hnX j hj, star_zero]
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, gram_apply, gram_apply]
  by_cases hi : i = j₀
  · by_cases hj : j = j₀
    · subst hi; subst hj
      simp only [Function.update_self, star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
        dotProduct_smul, hn1, hx₀, hx₀', Matrix.single_apply_same, smul_eq_mul, mul_zero, mul_one, add_zero, zero_add]
      rw [Complex.normSq_eq_conj_mul_self, mul_comm ζ]; rfl
    · subst hi
      simp only [Function.update_self, Function.update_of_ne hj, star_add, star_smul, add_dotProduct, smul_dotProduct,
        hnX j hj, smul_eq_mul, mul_zero, add_zero]
      rw [Matrix.single_apply_of_col_ne _ _ (Ne.symm hj)]; simp
  · by_cases hj : j = j₀
    · subst hj
      simp only [Function.update_self, Function.update_of_ne hi, dotProduct_add, dotProduct_smul,
        hnX' i hi, smul_eq_mul, mul_zero, add_zero]
      rw [Matrix.single_apply_of_row_ne (Ne.symm hi)]; simp
    · simp only [Function.update_of_ne hi, Function.update_of_ne hj]
      rw [Matrix.single_apply_of_row_ne (Ne.symm hi)]; simp
end Formalism.FourierDecayAlt.P.HermitianFormFactor
