-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials.prod_abs_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:08:26.846024+00:00
-- url     : https://prove2.me/submissions/9794b3ce-61a2-49e7-b096-87adfc3a9634

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
theorem _root_.solution (j k : ℕ) :
    ∏ i ∈ range (j + 1 + k), (if i = j then (1:ℝ) else |(j:ℝ) - i|) = j.factorial * k.factorial := by
  rw [prod_range_add, prod_range_succ, if_pos rfl, mul_one]
  congr 1
  · rw [← prod_range_reflect, ← prod_range_add_one_eq_factorial]
    push_cast
    refine prod_congr rfl fun i hi => ?_
    have hi' : i < j := mem_range.mp hi
    rw [if_neg (by omega)]
    have : ((j - 1 - i : ℕ) : ℝ) = (j:ℝ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this, abs_of_nonneg (by ring_nf; positivity)]
    ring
  · rw [← prod_range_add_one_eq_factorial]
    push_cast
    refine prod_congr rfl fun i _ => ?_
    rw [if_neg (by omega)]
    rw [abs_sub_comm, abs_of_nonneg (by ring_nf; positivity)]
    ring
end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials
