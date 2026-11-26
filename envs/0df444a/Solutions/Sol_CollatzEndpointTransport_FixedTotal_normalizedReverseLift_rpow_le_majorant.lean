-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.normalizedReverseLift_rpow_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:19.167027+00:00
-- url     : https://prove2.me/submissions/da96e24d-e755-4862-82d8-04322915f8b9

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
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
theorem _root_.solution
    {theta : ℝ} (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    ∀ ks : List ℕ,
      (normalizedReverseLift ks) ^ theta ≤
        reverseMomentMajorant theta ks := by
  intro ks
  induction ks with
  | nil => simp
  | cons k ks ih =>
      rw [normalizedReverseLift_cons, reverseMomentMajorant_cons,
        NNReal.div_rpow]
      have hden : 0 < (((2 : ℝ≥0) ^ k) ^ theta) :=
        NNReal.rpow_pos (by positivity)
      apply (div_le_div_iff_of_pos_right hden).2
      calc
        (1 + 3 * normalizedReverseLift ks) ^ theta
            ≤ (1 : ℝ≥0) ^ theta +
                (3 * normalizedReverseLift ks) ^ theta :=
          NNReal.rpow_add_le_add_rpow 1 (3 * normalizedReverseLift ks)
            htheta0 htheta1
        _ = 1 + (3 : ℝ≥0) ^ theta *
              (normalizedReverseLift ks) ^ theta := by
          rw [NNReal.one_rpow, NNReal.mul_rpow]
        _ ≤ 1 + (3 : ℝ≥0) ^ theta *
              reverseMomentMajorant theta ks := by
          gcongr
end CollatzEndpointTransport.FixedTotal
