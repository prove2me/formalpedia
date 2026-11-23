-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.normal_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:36.981567+00:00
-- url     : https://prove2.me/submissions/042da725-3044-4bf9-80d0-5257c40d2ea0

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_eq_zero_of_form

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (M E : Matrix (Fin n) (Fin n) ℂ) (hM : M * M = M) (hadj : Mᴴ * Hc = Hc * E)
    (hc : E * M = M * E) : E = M := by
  have hHh : Hcᴴ = Hc := hH.isHermitian
  have hE : Eᴴ * Hc = Hc * M := by
    have := congrArg Matrix.conjTranspose hadj
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hHh] at this
    exact this.symm
  have A : ∀ X : Matrix (Fin n) (Fin n) ℂ, Mᴴ * (Hc * X) = Hc * (E * X) := fun X => by
    rw [← Matrix.mul_assoc, hadj, Matrix.mul_assoc]
  have B : ∀ X : Matrix (Fin n) (Fin n) ℂ, Eᴴ * (Hc * X) = Hc * (M * X) := fun X => by
    rw [← Matrix.mul_assoc, hE, Matrix.mul_assoc]
  have MM : ∀ X : Matrix (Fin n) (Fin n) ℂ, M * (M * X) = M * X := fun X => by
    rw [← Matrix.mul_assoc, hM]
  have EM : ∀ X : Matrix (Fin n) (Fin n) ℂ, E * (M * X) = M * (E * X) := fun X => by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  have h1 : M - M * E = 0 := by
    apply eq_zero_of_form hH
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, sub_mul, mul_sub,
      Matrix.mul_assoc, A, B, MM, EM, hM, hc]
    abel
  have h2 : E - M * E = 0 := by
    apply eq_zero_of_form hH
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, sub_mul, mul_sub,
      Matrix.mul_assoc, A, B, MM, EM, hM, hc]
    abel
  rw [sub_eq_zero] at h1 h2
  exact h2.trans h1.symm
end Formalism.DivisionValues.FinitelyNonzeroLinear
