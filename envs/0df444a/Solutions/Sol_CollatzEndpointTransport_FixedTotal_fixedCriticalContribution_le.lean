-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedCriticalContribution_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:24.271747+00:00
-- url     : https://prove2.me/submissions/f590a953-3c48-4a68-b2f1-39562b958e49

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedCriticalNumerator_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_sqrt_div_sqrt_card_le_sqrt_sum
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) :
    fixedCriticalContribution N s ≤
      4 * Real.sqrt
        (∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) := by
  by_cases hcard : (fixedSet N s).card = 0
  · have hset : fixedSet N s = ∅ := Finset.card_eq_zero.mp hcard
    simp [fixedCriticalContribution, fixedCriticalNumerator,
      fixedFiberCard, hset, residueFiber]
  have hsqrtCard :
      0 < Real.sqrt ((fixedSet N s).card : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast (Nat.pos_of_ne_zero hcard)
  calc
    fixedCriticalContribution N s
        ≤ (4 * ∑ c ∈ fixedSet N s,
            Real.sqrt (3 ^ s + syracuseNumerator c)) /
            Real.sqrt (fixedSet N s).card := by
      exact div_le_div_of_nonneg_right
        (fixedCriticalNumerator_le N s) (Real.sqrt_nonneg _)
    _ = 4 * ((∑ c ∈ fixedSet N s,
            Real.sqrt (3 ^ s + syracuseNumerator c)) /
            Real.sqrt (fixedSet N s).card) := by
      ring
    _ ≤ 4 * Real.sqrt
        (∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) := by
      have hsqrt :=
        sum_sqrt_div_sqrt_card_le_sqrt_sum
          (fixedSet N s) (fun c => 3 ^ s + syracuseNumerator c)
      norm_num [Nat.cast_add, Nat.cast_pow] at hsqrt ⊢
      nlinarith
end CollatzEndpointTransport.FixedTotal
