-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lift_top_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:20.506396+00:00
-- url     : https://prove2.me/submissions/b2746138-9171-4471-8e99-a7e03c4ad0a8

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_isTop_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_isTop_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_pairing_top_degree
import Theorems.Thm_Formalism_FourierDecayAlt_P_j_pairing_formula

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.TopDegreePolynomials
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.F7.LiftTop := by
  intro R M _ _ _ _ _ _ Ξ n s A B Av Bv A₀ A₀v e t t' h X X' _ he ht ht' hA hAn hAv hAvn
    hA₀ hA₀n hA₀v hA₀vn hB hBv
  have cA : A.coeff (n + s) = 1 := by rw [← hAn]; exact hA.coeff_natDegree
  have cAv : Av.coeff (n + s) = 1 := by rw [← hAvn]; exact hAv.coeff_natDegree
  have cA₀ : A₀.coeff n = 1 := by rw [← hA₀n]; exact hA₀.coeff_natDegree
  have cA₀v : A₀v.coeff n = 1 := by rw [← hA₀vn]; exact hA₀v.coeff_natDegree
  have h1 := isTop_const_mul (e * t⁻¹)
    (pairing_top_degree R M Ξ A₀ Av n (n + s) h X X' hA₀n.le hAvn.le)
  have h2 := isTop_const_mul (e * t'⁻¹)
    (pairing_top_degree R M Ξ A A₀v (n + s) n h X X' hAn.le hA₀vn.le)
  have e1 : n + (n + s) = 2 * n + s := by ring
  have e2 : n + s + n = 2 * n + s := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 := isTop_sub h1 h2
  have hce : (starRingEnd ℂ) e = e := by
    rcases he with rfl | rfl <;> simp
  convert h3 using 1
  · funext Y
    have := j_pairing_formula R M Ξ A B Av Bv 0 Y (Y + h) X X'
    have hU : Formalism.YangianSpanCharacter.T.Uinv (A := R) (0 : ℂ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Uinv]
    rw [hU, mul_one] at this
    rw [this, map_zero, zero_mul, add_zero, hB, hBv, map_smul Ξ, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ (Ξ (evR A Y • X))]
    simp [hce]
  · simp [cA, cAv, cA₀, cA₀v]
    ring
end Formalism.FourierDecayAlt.P
