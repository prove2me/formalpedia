-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.plane_wave_top_degree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:53.424958+00:00
-- url     : https://prove2.me/submissions/c9d0672a-6ef0-4088-be1d-ff82638c7c41

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopDegreePolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_TopDegreePolynomials_isTop_sub
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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.PlaneWaveTop := by
  intro R M _ _ _ _ _ _ Ξ n A B Av Bv s X X' hS hSv
  obtain ⟨hA, hAn, hB⟩ := hS
  obtain ⟨hAv, hAvn, hBv⟩ := hSv
  have cA : A.coeff n = 1 := by rw [← hAn]; exact hA.coeff_natDegree
  have cAv : Av.coeff n = 1 := by rw [← hAvn]; exact hAv.coeff_natDegree
  have cB : B.coeff n = 0 := coeff_eq_zero_of_degree_lt hB
  have cBv : Bv.coeff n = 0 := coeff_eq_zero_of_degree_lt hBv
  have dB : B.natDegree ≤ n := natDegree_le_of_degree_le hB.le
  have dBv : Bv.natDegree ≤ n := natDegree_le_of_degree_le hBv.le
  have h1 := pairing_top_degree R M Ξ (B + C (algebraMap ℂ R s) * A) Av n n 1 X X'
    (natDegree_add_le_of_degree_le dB ((natDegree_C_mul_le _ _).trans hAn.le)) hAvn.le
  have h2 := pairing_top_degree R M Ξ A Bv n n 1 X X' hAn.le dBv
  have h3 := isTop_sub h1 h2
  rw [two_mul]
  convert h3 using 1
  · funext Y
    rw [j_pairing_formula R M Ξ A B Av Bv s Y (Y + 1) X X']
    simp [evR, eval_add, eval_C_mul]
  · simp [cA, cAv, cB, cBv, algebraMap_smul]
end Formalism.FourierDecayAlt.P
