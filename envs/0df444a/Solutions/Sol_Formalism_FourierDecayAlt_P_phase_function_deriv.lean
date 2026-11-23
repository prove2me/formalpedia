-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.phase_function_deriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:27.944616+00:00
-- url     : https://prove2.me/submissions/ef0f1739-1e15-460e-ad90-d01593cf3dd0

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_prod_split
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_phase_function_update
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_phase_deriv_update
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_hasDerivAt_inv_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_G1_hasDerivAt_inv_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.PhaseFunctionDeriv := by
  intro n D' x hx
  have hQ : ∀ k, (∏ j ∈ univ \ {k}, x j) ≠ 0 := fun k => Finset.prod_ne_zero_iff.mpr (fun j _ => hx j)
  constructor
  · intro k
    rw [show (fun ξ => g0 D' (Function.update x k ξ)) = fun ξ =>
      ξ + ∑ j ∈ univ \ {k}, x j + D' / (ξ * ∏ j ∈ univ \ {k}, x j) from funext (phase_function_update D' x k)]
    have h := ((hasDerivAt_id' (x k)).add_const (∑ j ∈ univ \ {k}, x j)).add
      (hasDerivAt_inv_lin D' _ (x k) (hx k) (hQ k))
    refine h.congr_deriv ?_
    unfold dg0
    rw [prod_split x k]
    ring
  · intro i j
    rw [show (fun ξ => dg0 D' (Function.update x j ξ) i) = fun ξ =>
      1 - D' / (ξ * ∏ l ∈ univ \ {j}, x l) / (Function.update x j ξ i) from
      funext (phase_deriv_update D' x j i)]
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      have h := (hasDerivAt_inv_sq D' _ (x i) (hx i) (hQ i)).const_sub 1
      refine h.congr_deriv ?_
      unfold hess
      rw [prod_split x i]
      simp
    · simp only [Function.update_of_ne hij]
      have h := ((hasDerivAt_inv_lin D' _ (x j) (hx j) (hQ j)).div_const (x i)).const_sub 1
      refine h.congr_deriv ?_
      unfold hess
      rw [prod_split x j]
      have := hx i; have := hx j; have := hQ j
      simp only [if_neg hij]
      field_simp
end Formalism.FourierDecayAlt.P
