-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.sum_lagCo_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:31:40.871795+00:00
-- url     : https://prove2.me/submissions/cb312062-6f58-4a07-816a-172efd866546

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials

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
theorem _root_.solution {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ)
    (hk : k ≤ d) : ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by
  have hlt : ((X : ℝ[X]) ^ k).degree < (univ : Finset (Fin (d + 1))).card := by
    rw [degree_X_pow, card_univ, Fintype.card_fin]; exact_mod_cast Nat.lt_succ_of_le hk
  have h := Lagrange.coeff_eq_sum (s := univ) (v := y) hy.injOn hlt
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, coeff_X_pow, eval_pow, eval_X] at h
  have e : (if k = d then (1:ℝ) else 0) = if d = k then 1 else 0 := by
    by_cases hkd : k = d
    · subst hkd; simp
    · rw [if_neg hkd, if_neg (Ne.symm hkd)]
  rw [e, h]
  refine sum_congr rfl fun i _ => ?_
  unfold lagCo
  rw [prod_inv_distrib, div_eq_mul_inv, mul_comm]
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
