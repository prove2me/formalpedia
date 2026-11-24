-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.spacing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:46:37.791388+00:00
-- url     : https://prove2.me/submissions/ad79f8f7-3cbd-461f-ba4e-52f1315fdb59

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_chebPt_eq
import Theorems.Thm_Formalism_SA_P_node_sub_node_ge


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
theorem _root_.solution : Formalism.FourierDecayAlt.F7.ChebSpacing := by
  intro α β n hαβ hn j
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h := Formalism.SA.P.node_sub_node_ge (n := n) (i := j) (k := j + 1) hn (Nat.lt_succ_self _) j.isLt
  rw [chebPt_eq, chebPt_eq, abs_sub_comm]
  simp only [Fin.val_succ, Fin.val_castSucc]
  have e : ((((j:ℕ) + 1 : ℕ) : ℝ) - (j:ℕ)) = 1 := by push_cast; ring
  rw [e] at h
  have h2 : (β - α) / (n:ℝ) ^ 2 = (β - α) / 2 * (2 * 1 ^ 2 / (n:ℝ) ^ 2) := by ring
  have h3 : (β - α) / 2 * (2 * 1 ^ 2 / (n:ℝ) ^ 2) ≤
      (β - α) / 2 * (Chebyshev.node n j - Chebyshev.node n (j + 1)) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  rw [h2]
  refine h3.trans ((le_abs_self _).trans (le_of_eq ?_))
  congr 1; ring
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
