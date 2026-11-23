-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.node_mul_U
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:26.917951+00:00
-- url     : https://prove2.me/submissions/f61dd2b8-21ca-4346-b903-9deac3bcea97

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
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
theorem _root_.solution (m : ℕ) (j : Fin (m + 2)) :
    nd (m + 1) j * (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) =
      if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (-1) ^ (j:ℕ) * ((m:ℝ) + 1) else 0 := by
  by_cases h0 : (j:ℕ) = 0
  · have : nd (m + 1) j = 1 := by unfold nd; rw [h0]; exact Chebyshev.node_eq_one
    rw [this, if_pos (Or.inl h0), h0, Chebyshev.U_eval_one]; simp
  by_cases h1 : (j:ℕ) = m + 1
  · have : nd (m + 1) j = -1 := by unfold nd; rw [h1]; exact Chebyshev.node_eq_neg_one (by omega)
    rw [this, if_pos (Or.inr h1), h1, Chebyshev.U_eval_neg_one, Int.cast_negOnePow]
    push_cast
    rw [zpow_natCast, pow_succ]; ring
  · rw [if_neg (by tauto)]
    have h := U_mul_sin_node m j
    have hpos : 0 < Real.sin ((j:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ)) := by
      have hj : (0:ℝ) < (j:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hjm : ((j:ℕ):ℝ) < ((m + 1 : ℕ) : ℝ) := by
        have := j.isLt
        exact_mod_cast (by omega : (j:ℕ) < m + 1)
      have hm : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := Real.pi_pos; positivity
      · rw [div_lt_iff₀ hm, mul_comm]
        exact mul_lt_mul_of_pos_left hjm Real.pi_pos
    have : (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hpos.ne'
    rw [this, mul_zero]
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
