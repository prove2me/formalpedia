-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.theta_base_change_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:58.815831+00:00
-- url     : https://prove2.me/submissions/c8476bb0-97a1-4201-a0df-cbcfe359fd60

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_gamma_laws_hold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : ThetaBaseChange := by
  intro k _ n un g D
  obtain ⟨hadd, hmul, hC, -, hX, -, hcc0⟩ := gamma_laws_hold k 0 un
  have e1 : ∀ f : k⟦X⟧, coeff 1 (X * f) = constantCoeff f := by
    intro f
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have h1 : ∀ y : k⟦X⟧, coeff 1 (gam0 0 un y) = coeff 1 y := by
    intro y
    obtain ⟨q, hq⟩ : X ∣ y - C (constantCoeff y) := by
      rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
    have e : y = C (constantCoeff y) + X * q := by rw [← hq]; ring
    rw [e, hadd, hmul, hC, hX]
    rw [map_add, map_add, coeff_C, if_neg one_ne_zero, zero_add, zero_add]
    rw [mul_assoc, e1, e1, map_mul, hcc0]
    simp
  have hc1 : ∀ f q : k⟦X⟧, coeff 1 (f * q) = coeff 1 f * constantCoeff q + constantCoeff f * coeff 1 q := by
    intro f q
    first
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (rw [coeff_mul, Finset.Nat.antidiagonal_succ]; simp [coeff_zero_eq_constantCoeff_apply])
    | (rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul, Finset.Nat.antidiagonal_succ];
        simp [coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply]; ring)
    | (simp [coeff_mul, Finset.Nat.sum_antidiagonal_succ, coeff_zero_eq_constantCoeff_apply])
  have hcoef : ∀ M N : Matrix (Fin n) (Fin n) k⟦X⟧, (M * N).map (coeff 1) =
      M.map (coeff 1) * N.map constantCoeff + M.map constantCoeff * N.map (coeff 1) := by
    intro M N
    ext i j
    simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, hc1,
      Finset.sum_add_distrib]
  set A := ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) with hA
  set G := (g : Matrix (Fin n) (Fin n) k⟦X⟧) with hG
  have hAG : A * G = 1 := Units.inv_mul g
  have hGA : G * A = 1 := Units.mul_inv g
  have hone0 : (1 : Matrix (Fin n) (Fin n) k⟦X⟧).map constantCoeff = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hAG0 : A.map constantCoeff * G.map constantCoeff = 1 := by
    rw [← Matrix.map_mul, hAG, hone0]
  have hGA0 : G.map constantCoeff * A.map constantCoeff = 1 := by
    rw [← Matrix.map_mul, hGA, hone0]
  have hAG1 : A.map (coeff 1) * G.map constantCoeff + A.map constantCoeff * G.map (coeff 1) = 0 := by
    rw [← hcoef, hAG]
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hB0 : (1 + (X : k⟦X⟧) • D).map constantCoeff = 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply]
  have hB1 : (1 + (X : k⟦X⟧) • D).map (coeff 1) = D.map constantCoeff := by
    ext i j
    by_cases hij : i = j <;> simp [hij, Matrix.one_apply, e1]
  have hC0 : (G.map (gam0 0 un)).map constantCoeff = G.map constantCoeff := by
    ext i j
    simp only [Matrix.map_apply, hcc0]
  have hC1 : (G.map (gam0 0 un)).map (coeff 1) = G.map (coeff 1) := by
    ext i j
    simp only [Matrix.map_apply, h1]
  have hθ : thetaOf (chgGam un g D) = A.map constantCoeff * D.map constantCoeff * G.map constantCoeff := by
    show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map (coeff 1) = _
    rw [hcoef, hcoef, Matrix.map_mul, hB0, hB1, hC0, hC1, Matrix.mul_one, Matrix.mul_one,
      Matrix.add_mul, add_right_comm, hAG1, zero_add]
  refine ⟨?_, hθ, ?_⟩
  · show (A * (1 + (X : k⟦X⟧) • D) * G.map (gam0 0 un)).map constantCoeff = 1
    rw [Matrix.map_mul, Matrix.map_mul, hB0, Matrix.mul_one, hC0, hAG0]
  · rw [hθ, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hGA0, Matrix.one_mul]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
