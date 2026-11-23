-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.nodal_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:02.467858+00:00
-- url     : https://prove2.me/submissions/df9ee96e-17f7-45ea-aa82-e2ae1615699e

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_nd_injective
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_U_mul_sin_node

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
theorem _root_.solution (m : ℕ) :
    (X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ) = C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1)) := by
  have h2 : ((2:ℝ) ^ m) ≠ 0 := by positivity
  have hmon : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (R := ℝ) (1:ℝ) (n := 2) (by norm_num)
    simpa using this
  have hdX : (X ^ 2 - 1 : ℝ[X]).degree = 2 := by
    have := degree_X_pow_sub_C (R := ℝ) (n := 2) (by norm_num) (1:ℝ)
    simpa using this
  have hdL : ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, hdX, Chebyshev.degree_U_natCast]
    norm_cast; ring_nf
  have hdR : (C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1))).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_C_mul h2, Lagrange.degree_nodal, card_univ, Fintype.card_fin]
  apply Polynomial.eq_of_degree_le_of_eval_index_eq univ (v := nd (m + 1))
    ((nd_injective (m + 1)).injOn)
  · rw [hdL, card_univ, Fintype.card_fin]
  · exact hdL.trans hdR.symm
  · rw [leadingCoeff_mul, hmon.leadingCoeff, Chebyshev.leadingCoeff_U_natCast, leadingCoeff_mul,
        leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]; ring
  · intro i _
    rw [eval_mul, eval_mul, Lagrange.eval_nodal_at_node (mem_univ i), mul_zero]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    have h := U_mul_sin_node m i
    have hs : (nd (m + 1) i) ^ 2 - 1 = - Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ)) ^ 2 := by
      have := Real.sin_sq_add_cos_sq ((i:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ))
      unfold nd Chebyshev.node
      linarith
    rw [hs]
    unfold nd
    linear_combination (- Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ))) * h
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
