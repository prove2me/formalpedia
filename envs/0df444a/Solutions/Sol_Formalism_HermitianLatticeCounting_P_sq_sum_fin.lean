-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.sq_sum_fin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:29.568125+00:00
-- url     : https://prove2.me/submissions/af8c8aa2-4910-48a0-8229-29a16a57cc04

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {a : ℕ} (j : Fin a → ℕ) :
    (∑ x, j x) ^ 2 = (∑ x, j x ^ 2)
      + 2 * ∑ x, ∑ y ∈ univ.filter (fun y => x < y), j x * j y := by
  have h : ∀ x y : Fin a, j x * j y = (if x < y then j x * j y else 0)
      + (if y < x then j y * j x else 0) + (if x = y then j x ^ 2 else 0) := by
    intro x y
    rcases lt_trichotomy x y with h | h | h
    · simp [h, h.ne, h.le.not_gt]
    · subst h; simp [sq]
    · simp [h, h.ne', h.le.not_gt, mul_comm]
  rw [sq, Finset.sum_mul_sum]
  simp_rw [Finset.sum_filter]
  calc ∑ x, ∑ y, j x * j y
      = ∑ x, ∑ y, ((if x < y then j x * j y else 0)
      + (if y < x then j y * j x else 0) + (if x = y then j x ^ 2 else 0)) := by
        apply Finset.sum_congr rfl; intro x _
        apply Finset.sum_congr rfl; intro y _
        exact h x y
    _ = (∑ x, ∑ y, (if x < y then j x * j y else 0))
        + (∑ x, ∑ y, (if y < x then j y * j x else 0)) + ∑ x, ∑ y, (if x = y then j x ^ 2 else 0) := by
        simp_rw [Finset.sum_add_distrib]
    _ = _ := by
        rw [Finset.sum_comm (f := fun x y => if y < x then j y * j x else 0)]
        simp
        ring
end Formalism.HermitianLatticeCounting.P
