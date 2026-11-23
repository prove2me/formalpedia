-- Prove2me | solution 1 for Formalism.DivisionValues.OperatorNormFrames.opNorm_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:16.697849+00:00
-- url     : https://prove2.me/submissions/e01c3158-bfa3-4314-a5c9-5577ba67613e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_eq
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_nonneg
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_cnorm_star
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_norm_dot_le
import Theorems.Thm_Formalism_DivisionValues_OperatorNormFrames_star_dot_self
import Theorems.Thm_Formalism_HN_PlaceOperatorNorms_cnorm_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.OperatorNormFrames
namespace Formalism.DivisionValues.OperatorNormFrames
theorem _root_.solution {a D : ℕ} (A : Matrix (Fin D) (Fin a) ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖ ≤ c ↔
      ∀ (x : Fin a → ℂ) (y : Fin D → ℂ),
        ‖y ⬝ᵥ A.mulVec x‖ ≤ c * Formalism.HermitianLatticesTheory.cnorm x * Formalism.HermitianLatticesTheory.cnorm y := by
  have hT : ∀ x : Fin a → ℂ,
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A) (WithLp.toLp 2 x)‖ =
        Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) := by
    intro x
    rw [cnorm_eq]
    simp [Matrix.toEuclideanLin_apply]
  constructor
  · intro h x y
    have h2 : Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) ≤ c * Formalism.HermitianLatticesTheory.cnorm x := by
      rw [← hT, cnorm_eq x]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    calc ‖y ⬝ᵥ A.mulVec x‖ ≤ Formalism.HermitianLatticesTheory.cnorm y * Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) := norm_dot_le _ _
      _ ≤ Formalism.HermitianLatticesTheory.cnorm y * (c * Formalism.HermitianLatticesTheory.cnorm x) :=
          mul_le_mul_of_nonneg_left h2 (cnorm_nonneg y)
      _ = c * Formalism.HermitianLatticesTheory.cnorm x * Formalism.HermitianLatticesTheory.cnorm y := by ring
  · intro h
    refine ContinuousLinearMap.opNorm_le_bound _ hc fun z => ?_
    obtain ⟨x, rfl⟩ : ∃ x, z = WithLp.toLp 2 x := ⟨WithLp.ofLp z, by simp⟩
    rw [hT, ← cnorm_eq]
    have h3 := h x (star (A.mulVec x))
    rw [star_dot_self, cnorm_star] at h3
    have h4 : ‖((Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) ^ 2 : ℝ) : ℂ)‖ = Formalism.HermitianLatticesTheory.cnorm (A.mulVec x) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [h4] at h3
    have hN := cnorm_nonneg (A.mulVec x)
    have hX := cnorm_nonneg x
    nlinarith [mul_nonneg hc hX]
end Formalism.DivisionValues.OperatorNormFrames
