-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.residueFibers_renyi_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:02.496166+00:00
-- url     : https://prove2.me/submissions/13c6a937-e8b2-4edf-b60f-a84b46a10668

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_residueFiber_renyi_bound
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_residueFiber


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {alpha : Type*} [DecidableEq alpha]
    (W : Finset alpha) (A : alpha → ℕ) (m : ℕ)
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    (m : ℝ) ^ theta *
        (∑ a : Fin m,
          ((residueFiber W A m a).card : ℝ) *
            ((residueFiber W A m a).card : ℝ) ^ theta) ≤
      4 * ∑ x ∈ W, ((m + A x : ℕ) : ℝ) ^ theta := by
  calc
    (m : ℝ) ^ theta *
          (∑ a : Fin m,
            ((residueFiber W A m a).card : ℝ) *
              ((residueFiber W A m a).card : ℝ) ^ theta) =
        ∑ a : Fin m,
          (m : ℝ) ^ theta *
            ((residueFiber W A m a).card : ℝ) *
            ((residueFiber W A m a).card : ℝ) ^ theta := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ ∑ a : Fin m,
        4 * ∑ x ∈ residueFiber W A m a,
          ((m + A x : ℕ) : ℝ) ^ theta := by
      apply Finset.sum_le_sum
      intro a ha
      exact residueFiber_renyi_bound W A m a htheta0 htheta1 hm hA
    _ = 4 * ∑ x ∈ W, ((m + A x : ℕ) : ℝ) ^ theta := by
      rw [← Finset.mul_sum, sum_residueFiber W A m hm]
end CollatzEndpointTransport.FixedTotal
