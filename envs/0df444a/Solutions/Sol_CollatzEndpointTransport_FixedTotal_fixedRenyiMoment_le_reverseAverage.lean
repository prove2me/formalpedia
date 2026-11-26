-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_le_reverseAverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:48:37.125804+00:00
-- url     : https://prove2.me/submissions/435364d3-e1af-41ad-94ed-100c71add2a7

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedLiftMoment_div_scale_card_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedRenyiMoment_le
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
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hcard : 0 < (fixedSet N s).card) :
    fixedRenyiMoment N s theta ≤
      4 * (((2 : ℝ) ^ N) ^ theta) *
        fixedReverseMajorantAverage N s theta /
          (((fixedSet N s).card : ℝ) ^ theta) := by
  have hlift := fixedLiftMoment_div_scale_card_le
    htheta0.le htheta1 hcard
  have hscale : 0 < (((2 : ℝ) ^ N) ^ theta) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hcardR : 0 < ((fixedSet N s).card : ℝ) := by exact_mod_cast hcard
  have hlift' :
      fixedLiftMoment N s theta ≤
        (((2 : ℝ) ^ N) ^ theta) *
          ((fixedSet N s).card : ℝ) *
            fixedReverseMajorantAverage N s theta := by
      have hraw := (div_le_iff₀ (mul_pos hscale hcardR)).mp hlift
      simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  calc
    fixedRenyiMoment N s theta ≤
        4 * fixedLiftMoment N s theta /
          ((fixedSet N s).card : ℝ) ^ (1 + theta) :=
      fixedRenyiMoment_le N s htheta0 htheta1
    _ ≤ 4 * ((((2 : ℝ) ^ N) ^ theta) *
          ((fixedSet N s).card : ℝ) *
            fixedReverseMajorantAverage N s theta) /
          ((fixedSet N s).card : ℝ) ^ (1 + theta) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlift' (by norm_num))
        (Real.rpow_nonneg (by positivity) _)
    _ = 4 * (((2 : ℝ) ^ N) ^ theta) *
        fixedReverseMajorantAverage N s theta /
          (((fixedSet N s).card : ℝ) ^ theta) := by
      rw [show (1 : ℝ) + theta = theta + 1 by ring,
        Real.rpow_add_one hcardR.ne']
      field_simp
end CollatzEndpointTransport.FixedTotal
