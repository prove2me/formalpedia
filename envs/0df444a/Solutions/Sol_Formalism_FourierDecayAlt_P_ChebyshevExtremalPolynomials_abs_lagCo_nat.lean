-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.abs_lagCo_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:02.083872+00:00
-- url     : https://prove2.me/submissions/cf46beac-00d3-451e-9101-b0e0527165f2

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_ChebyshevLeadingCoeffHolds
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChebyshevExtremalPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChebyshevExtremalPolynomials_prod_abs_int

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
theorem _root_.solution (n : ℕ) (j : Fin (n + 1)) :
    |lagCo (fun i : Fin (n + 1) => ((i:ℕ):ℝ)) j| =
      ((j:ℕ).factorial * (n - (j:ℕ)).factorial : ℝ)⁻¹ := by
  unfold lagCo
  rw [prod_inv_distrib, abs_inv, abs_prod]
  congr 1
  have h1 : ∏ i ∈ univ.erase j, |(((j:ℕ):ℝ)) - ((i:ℕ):ℝ)| =
      ∏ i : Fin (n + 1), (if (i:ℕ) = (j:ℕ) then (1:ℝ) else |((j:ℕ):ℝ) - ((i:ℕ):ℝ)|) := by
    rw [← mul_prod_erase univ _ (mem_univ j), if_pos rfl, one_mul]
    refine prod_congr rfl fun i hi => ?_
    rw [if_neg (fun h => (mem_erase.mp hi).1 (Fin.ext h))]
  rw [h1, Fin.prod_univ_eq_prod_range (fun i => if i = (j:ℕ) then (1:ℝ) else |((j:ℕ):ℝ) - (i:ℝ)|) (n + 1)]
  have hj := j.isLt
  have e : n + 1 = (j:ℕ) + 1 + (n - (j:ℕ)) := by omega
  have h2 := prod_abs_int (j:ℕ) (n - (j:ℕ))
  rw [← e] at h2
  exact h2
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
