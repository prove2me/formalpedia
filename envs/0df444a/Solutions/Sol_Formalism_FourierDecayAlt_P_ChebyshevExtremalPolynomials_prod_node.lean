-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.prod_node
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:02.462103+00:00
-- url     : https://prove2.me/submissions/2f300599-ad5b-4d20-bbf4-8a95f09a3a6e

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_nodal_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_deriv_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_node_mul_U

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
theorem _root_.solution (m : ℕ) (j : Fin (m + 2)) :
    (2:ℝ) ^ m * ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) =
      (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) := by
  have h1 := congrArg (fun p => eval (nd (m + 1) j) (derivative p)) (nodal_eq m)
  simp only [deriv_eq, derivative_C_mul, eval_mul, eval_C, eval_add, eval_X, eval_natCast, eval_one,
    Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ j), Lagrange.eval_nodal] at h1
  rw [← h1, node_mul_U]
  have hT : (Chebyshev.T ℝ ((m:ℤ) + 1)).eval (nd (m + 1) j) = (-1) ^ (j:ℕ) := by
    have := Chebyshev.eval_T_real_node (n := m + 1) (i := j) (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))
    push_cast at this
    exact this
  rw [hT]
  split_ifs <;> ring
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
