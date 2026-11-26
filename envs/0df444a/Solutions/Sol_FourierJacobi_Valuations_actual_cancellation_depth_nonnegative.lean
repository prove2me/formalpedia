-- Prove2me | solution 1 for FourierJacobi.Valuations.actual_cancellation_depth_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:46.355449+00:00
-- url     : https://prove2.me/submissions/686e30af-f809-4ba0-98ea-35b94e07bc85

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge

set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]
namespace FourierJacobi.Valuations
theorem _root_.solution (v : AddValuation K (WithTop ℤ))
    (x y z : K) (r j h c : ℤ)
    (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (heq : 2 * h = j - r) (hc : v (y ^ 2 / (x * z) - 1) = c) : 0 ≤ c := by
  have hratio : v (y ^ 2 / (x * z)) = 0 := by
    have hval : v (y ^ 2 / (x * z)) = ((2 * h - (j - r) : ℤ) : WithTop ℤ) := by
      simp [hj, hh, hz, two_nsmul, two_mul, sub_eq_add_neg]
    rw [hval, heq]
    simp
  have hv := v.map_sub (y ^ 2 / (x * z)) 1
  rw [hratio, v.map_one, min_self, hc] at hv
  exact_mod_cast hv
end FourierJacobi.Valuations
