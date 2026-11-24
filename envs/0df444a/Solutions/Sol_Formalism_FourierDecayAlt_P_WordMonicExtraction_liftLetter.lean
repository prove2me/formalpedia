-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.liftLetter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:51.800818+00:00
-- url     : https://prove2.me/submissions/a865db1e-c694-441e-a87f-441a6e0c48ff

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_isTop_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_isTop_const_mul
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
theorem _root_.solution (Ξ : Sesq M) (n s : ℕ) (D : Dat R) (A₀ A₀v : R[X]) (e t t' : ℂ) (x x' : M)
    (hs : D.s = 0) (he : e = 1 ∨ e = -1)
    (hA : D.A.Monic) (hAn : D.A.natDegree = n + s) (hAv : D.Av.Monic) (hAvn : D.Av.natDegree = n + s)
    (hA₀ : A₀.Monic) (hA₀n : A₀.natDegree = n) (hA₀v : A₀v.Monic) (hA₀vn : A₀v.natDegree = n)
    (hB : ∀ Y Y' : ℝ, Ξ (evR D.B Y • x) (evR D.Av Y' • x') =
      Ξ ((e * t⁻¹) • evR A₀ Y • x) (evR D.Av Y' • x'))
    (hBv : ∀ Y Y' : ℝ, Ξ (evR D.A Y • x) (evR D.Bv Y' • x') =
      Ξ (evR D.A Y • x) ((e * (starRingEnd ℂ t')⁻¹) • evR A₀v Y' • x')) :
    IsTopCoeff (fun Y => letterVal Ξ D Y x x') (2 * n + s) (e * (1 / t - 1 / t') * Ξ x x') := by
  have hA1 : D.A.coeff (n + s) = 1 := by
    rw [← hAn]
    exact hA.coeff_natDegree
  have hAv1 : D.Av.coeff (n + s) = 1 := by
    rw [← hAvn]
    exact hAv.coeff_natDegree
  have hA₀1 : A₀.coeff n = 1 := by
    rw [← hA₀n]
    exact hA₀.coeff_natDegree
  have hA₀v1 : A₀v.coeff n = 1 := by
    rw [← hA₀vn]
    exact hA₀v.coeff_natDegree
  have hce : starRingEnd ℂ e = e := by
    rcases he with rfl | rfl <;> simp
  have t1 := isTop_const_mul (e * t⁻¹) (pairTop Ξ A₀ D.Av n (n + s) 1 x x' hA₀n.le hAvn.le)
  have t2 := isTop_const_mul (e * t'⁻¹) (pairTop Ξ D.A A₀v (n + s) n 1 x x' hAn.le hA₀vn.le)
  have hdeg1 : n + (n + s) = 2 * n + s := by ring
  have hdeg2 : n + s + n = 2 * n + s := by ring
  rw [hdeg1] at t1
  rw [hdeg2] at t2
  have ht := isTop_sub t1 t2
  have hfun : (fun Y => letterVal Ξ D Y x x') = (fun Y =>
      e * t⁻¹ * Ξ (evR A₀ Y • x) (evR D.Av (Y + 1) • x') -
        e * t'⁻¹ * Ξ (evR D.A Y • x) (evR A₀v (Y + 1) • x')) := by
    funext Y
    unfold letterVal
    rw [hs, map_zero, zero_mul, add_zero, hB Y (Y + 1), hBv Y (Y + 1)]
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul,
      map_inv₀, Complex.conj_conj, hce]
  rw [hfun]
  convert ht using 1
  simp only [hA1, hAv1, hA₀1, hA₀v1, one_smul, one_div]
  ring
end Formalism.FourierDecayAlt.P.WordMonicExtraction
