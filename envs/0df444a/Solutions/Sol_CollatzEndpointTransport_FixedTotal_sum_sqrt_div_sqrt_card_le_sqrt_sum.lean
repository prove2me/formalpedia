-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_sqrt_div_sqrt_card_le_sqrt_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:31:54.140911+00:00
-- url     : https://prove2.me/submissions/367ed48c-ab1c-4a7e-8b1a-3500d02e6da9

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
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
    {α : Type*} [DecidableEq α]
    (W : Finset α) (q : α → ℕ) :
    (∑ x ∈ W, Real.sqrt (q x)) / Real.sqrt W.card ≤
      Real.sqrt (∑ x ∈ W, q x) := by
  by_cases hW : W = ∅
  · simp [hW]
  have hcard : 0 < W.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW)
  have hcardR : (0 : ℝ) < W.card := by exact_mod_cast hcard
  have hsqrtCard : 0 < Real.sqrt (W.card : ℝ) :=
    Real.sqrt_pos.mpr hcardR
  have hcs :
      (∑ x ∈ W, Real.sqrt (q x)) ^ 2 ≤
        (W.card : ℝ) * ∑ x ∈ W, (q x : ℝ) := by
    have hraw :=
      (sq_sum_le_card_mul_sum_sq
        (s := W) (f := fun x => Real.sqrt (q x)))
    calc
      (∑ x ∈ W, Real.sqrt (q x)) ^ 2
          ≤ (W.card : ℝ) *
              ∑ x ∈ W, (Real.sqrt (q x)) ^ 2 := hraw
      _ = (W.card : ℝ) * ∑ x ∈ W, (q x : ℝ) := by
        apply congrArg (fun z : ℝ => (W.card : ℝ) * z)
        apply Finset.sum_congr rfl
        intro x hx
        exact Real.sq_sqrt (by positivity)
  have hsumNonneg : 0 ≤ ∑ x ∈ W, (q x : ℝ) := by positivity
  have hsumSqrtNonneg :
      0 ≤ ∑ x ∈ W, Real.sqrt (q x) := by positivity
  apply (div_le_iff₀ hsqrtCard).2
  rw [← Real.sqrt_mul hsumNonneg]
  apply (Real.le_sqrt hsumSqrtNonneg
    (mul_nonneg hsumNonneg (by positivity))).2
  nlinarith
end CollatzEndpointTransport.FixedTotal
