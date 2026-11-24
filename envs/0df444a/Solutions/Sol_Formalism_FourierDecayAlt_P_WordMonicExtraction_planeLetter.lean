-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.planeLetter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:51.818771+00:00
-- url     : https://prove2.me/submissions/208b0863-29d0-408d-8ae5-867e3a6b1c1a

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_isTop_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_pairTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution (Ξ : Sesq M) (n : ℕ) (D : Dat R) (x x' : M) (hS : Shape n D.A D.B)
    (hSv : Shape n D.Av D.Bv) :
    IsTopCoeff (fun Y => letterVal Ξ D Y x x') (2 * n) (D.s * Ξ x x') := by
  obtain ⟨hAm, hAn, hBd⟩ := hS
  obtain ⟨hAvm, hAvn, hBvd⟩ := hSv
  have hBn : D.B.natDegree ≤ n := Polynomial.natDegree_le_of_degree_le hBd.le
  have hBvn : D.Bv.natDegree ≤ n := Polynomial.natDegree_le_of_degree_le hBvd.le
  have hB0 : D.B.coeff n = 0 := Polynomial.coeff_eq_zero_of_degree_lt hBd
  have hBv0 : D.Bv.coeff n = 0 := Polynomial.coeff_eq_zero_of_degree_lt hBvd
  have hA1 : D.A.coeff n = 1 := by
    rw [← hAn]
    exact hAm.coeff_natDegree
  have hAv1 : D.Av.coeff n = 1 := by
    rw [← hAvn]
    exact hAvm.coeff_natDegree
  have hP₁n : (D.B + Polynomial.C (algebraMap ℂ R D.s) * D.A).natDegree ≤ n :=
    (Polynomial.natDegree_add_le _ _).trans
      (max_le hBn ((Polynomial.natDegree_C_mul_le _ _).trans hAn.le))
  have hev : ∀ Y : ℝ, evR D.B Y + algebraMap ℂ R D.s * evR D.A Y =
      evR (D.B + Polynomial.C (algebraMap ℂ R D.s) * D.A) Y := by
    intro Y
    simp only [evR, Polynomial.eval_add, Polynomial.eval_C_mul]
  have t1 := pairTop Ξ (D.B + Polynomial.C (algebraMap ℂ R D.s) * D.A) D.Av n n 1 x x' hP₁n hAvn.le
  have t2 := pairTop Ξ D.A D.Bv n n 1 x x' hAn.le hBvn
  have ht := isTop_sub t1 t2
  unfold letterVal
  simp_rw [hev]
  rw [two_mul]
  convert ht using 1
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, hB0, hA1, hAv1, hBv0, zero_add, mul_one,
    one_smul, zero_smul, map_zero, sub_zero, algebraMap_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul]
end Formalism.FourierDecayAlt.P.WordMonicExtraction
