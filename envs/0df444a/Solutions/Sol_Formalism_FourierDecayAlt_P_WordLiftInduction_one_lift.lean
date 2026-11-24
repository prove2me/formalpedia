-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordLiftInduction.one_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:49.296864+00:00
-- url     : https://prove2.me/submissions/2c411ffd-a07f-49a1-9bf8-a8944cb7fd06

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordLiftInduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_isTop_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_isTop_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_pairing_top_degree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordLiftInduction
open Finset Polynomial Formalism.FourierDecayAlt.F7
variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]
namespace Formalism.FourierDecayAlt.P.WordLiftInduction
theorem _root_.solution (Ξ : Sesq M) (n s : ℕ) (D : Dat R) (A₀ A₀v : R[X]) (e t t' : ℂ) (X X' : M)
    (hs : D.s = 0) (he : e = 1 ∨ e = -1)
    (hA : D.A.Monic ∧ D.A.natDegree = n + s ∧ D.Av.Monic ∧ D.Av.natDegree = n + s)
    (hA₀ : A₀.Monic ∧ A₀.natDegree = n ∧ A₀v.Monic ∧ A₀v.natDegree = n)
    (h1 : ∀ (Y : ℝ) (Q Q' : R), Ξ (evR D.B Y • Q • X) (Q' • X') =
      Ξ ((e * t⁻¹) • evR A₀ Y • Q • X) (Q' • X'))
    (h2 : ∀ (Y : ℝ) (Q Q' : R), Ξ (Q • X) (evR D.Bv Y • Q' • X') =
      Ξ (Q • X) ((e * (starRingEnd ℂ t')⁻¹) • evR A₀v Y • Q' • X'))
    (Q Q' : R) :
    IsTopCoeff (fun Y => one Ξ D Y (Q • X) (Q' • X')) (2 * n + s)
      (e * (1 / t - 1 / t') * Ξ (Q • X) (Q' • X')) := by
  obtain ⟨hAm, hAd, hAvm, hAvd⟩ := hA
  obtain ⟨hA₀m, hA₀d, hA₀vm, hA₀vd⟩ := hA₀
  have p1 := pairing_top_degree R M Ξ A₀ D.Av n (n + s) 1 (Q • X) (Q' • X') hA₀d.le hAvd.le
  have p2 := pairing_top_degree R M Ξ D.A A₀v (n + s) n 1 (Q • X) (Q' • X') hAd.le hA₀vd.le
  have c1 : A₀.coeff n = 1 := by rw [← hA₀d]; exact hA₀m.coeff_natDegree
  have c2 : D.Av.coeff (n + s) = 1 := by rw [← hAvd]; exact hAvm.coeff_natDegree
  have c3 : D.A.coeff (n + s) = 1 := by rw [← hAd]; exact hAm.coeff_natDegree
  have c4 : A₀v.coeff n = 1 := by rw [← hA₀vd]; exact hA₀vm.coeff_natDegree
  rw [c1, c2, one_smul, one_smul, show n + (n + s) = 2 * n + s by ring] at p1
  rw [c3, c4, one_smul, one_smul, show n + s + n = 2 * n + s by ring] at p2
  have hce : starRingEnd ℂ e = e := by
    rcases he with rfl | rfl <;> simp
  have key := TopDegreePolynomials.isTop_sub (TopDegreePolynomials.isTop_const_mul (e * t⁻¹) p1) (TopDegreePolynomials.isTop_const_mul (e * t'⁻¹) p2)
  have hfun : (fun Y : ℝ => one Ξ D Y (Q • X) (Q' • X')) = fun Y : ℝ =>
      e * t⁻¹ * Ξ (evR A₀ Y • Q • X) (evR D.Av (Y + 1) • Q' • X') -
        e * t'⁻¹ * Ξ (evR D.A Y • Q • X) (evR A₀v (Y + 1) • Q' • X') := by
    funext Y
    unfold one
    rw [hs, map_zero, zero_mul, add_zero]
    congr 1
    · rw [← mul_smul (evR D.Av (Y + 1)) Q' X', h1, LinearMap.map_smul Ξ, LinearMap.smul_apply, smul_eq_mul]
    · rw [← mul_smul (evR D.A Y) Q X, h2, LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_inv₀,
        Complex.conj_conj, hce]
  rw [hfun]
  have hc : e * (1 / t - 1 / t') * Ξ (Q • X) (Q' • X') =
      e * t⁻¹ * Ξ (Q • X) (Q' • X') - e * t'⁻¹ * Ξ (Q • X) (Q' • X') := by
    rw [one_div, one_div]; ring
  rw [hc]
  exact key
end Formalism.FourierDecayAlt.P.WordLiftInduction
