-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_eq_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:08.735942+00:00
-- url     : https://prove2.me/submissions/ec52eb0e-7ccb-46b5-b00e-ab806bb3b064

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentTerm_cons_zero
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentTerm_cons_succ
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMoment_tail_cons
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


attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
open Finset
open scoped NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (theta : ℝ) :
    ∀ ks : List ℕ,
      reverseMomentMajorant theta ks = reverseMomentSeries theta ks := by
  intro ks
  induction ks with
  | nil => simp [reverseMomentSeries]
  | cons k ks ih =>
      rw [reverseMomentMajorant_cons, reverseMomentSeries]
      rw [reverseMoment_tail_cons]
      simp only [List.length_cons]
      rw [Finset.sum_range_succ', reverseMomentTerm_cons_zero]
      rw [Finset.sum_congr rfl (fun i _ => reverseMomentTerm_cons_succ theta k ks i),
        ← Finset.mul_sum, ih, reverseMomentSeries]
      have hk : (((2 : ℝ≥0) ^ k) ^ theta) ≠ 0 :=
        (NNReal.rpow_pos (by positivity)).ne'
      have hs : (((2 : ℝ≥0) ^ ks.sum) ^ theta) ≠ 0 :=
        (NNReal.rpow_pos (by positivity)).ne'
      field_simp
      ring
end CollatzEndpointTransport.FixedTotal
