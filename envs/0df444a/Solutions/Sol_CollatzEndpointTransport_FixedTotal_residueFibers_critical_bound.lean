-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.residueFibers_critical_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:19.007799+00:00
-- url     : https://prove2.me/submissions/925ead4c-b327-4f56-9163-7a9dde779c69

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_residueFiber_critical_bound
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_residueFiber

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {α : Type*} [DecidableEq α]
    (W : Finset α) (A : α → ℕ) (m : ℕ)
    (hm : 0 < m) (hA : Set.InjOn A W) :
    Real.sqrt m *
        (∑ a : Fin m,
          ((residueFiber W A m a).card : ℝ) *
            Real.sqrt (residueFiber W A m a).card) ≤
      4 * ∑ x ∈ W, Real.sqrt (m + A x) := by
  have hsum :
      (∑ a : Fin m,
          Real.sqrt m *
            ((residueFiber W A m a).card : ℝ) *
            Real.sqrt (residueFiber W A m a).card) ≤
        ∑ a : Fin m,
          4 * ∑ x ∈ residueFiber W A m a,
            Real.sqrt (m + A x) := by
    apply Finset.sum_le_sum
    intro a ha
    exact residueFiber_critical_bound W A m a hm hA
  calc
    Real.sqrt m *
        (∑ a : Fin m,
          ((residueFiber W A m a).card : ℝ) *
            Real.sqrt (residueFiber W A m a).card)
        =
      ∑ a : Fin m,
        Real.sqrt m *
          ((residueFiber W A m a).card : ℝ) *
          Real.sqrt (residueFiber W A m a).card := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ ≤ ∑ a : Fin m,
        4 * ∑ x ∈ residueFiber W A m a,
          Real.sqrt (m + A x) := hsum
    _ = 4 * ∑ a : Fin m,
        ∑ x ∈ residueFiber W A m a,
          Real.sqrt (m + A x) := by
      rw [Finset.mul_sum]
    _ = 4 * ∑ x ∈ W, Real.sqrt (m + A x) := by
      rw [sum_residueFiber W A m hm]
end CollatzEndpointTransport.FixedTotal
