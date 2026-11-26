-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_div_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:48:20.63929+00:00
-- url     : https://prove2.me/submissions/483cd4ea-c542-4b9e-b3a2-0a80c831a586

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseTermSum_div_card_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_nonneg
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiRatio_lt_one
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
    (htheta : 0 < theta)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta) :
    fixedReverseNonterminalSum N s theta /
        ((fixedSet N s).card : ℝ) ≤
      (N : ℝ) * (3 : ℝ) ^ (-theta) /
        (1 - centralRenyiRatio theta
          (centralSeparatorProportion N s)) := by
  let R := centralRenyiRatio theta (centralSeparatorProportion N s)
  have hpi0 : 0 < centralSeparatorProportion N s := by
    unfold centralSeparatorProportion
    have hsPos : 0 < (s - 1 : ℕ) := by omega
    have hNPos : 0 < (N - 1 : ℕ) := by omega
    exact div_pos (by exact_mod_cast hsPos) (by exact_mod_cast hNPos)
  have hR0 : 0 ≤ R := centralRenyiRatio_nonneg htheta hpi0.le
  have hR1 : R < 1 :=
    centralRenyiRatio_lt_one htheta hpi0 hpiAlpha
  have hsummable : Summable fun r : ℕ =>
      (N : ℝ) * (3 : ℝ) ^ (-theta) * R ^ r :=
    (summable_geometric_of_lt_one hR0 hR1).mul_left
      ((N : ℝ) * (3 : ℝ) ^ (-theta))
  unfold fixedReverseNonterminalSum
  rw [div_eq_mul_inv, Finset.sum_mul]
  calc
    (∑ r ∈ Ico 1 s,
        fixedReverseTermSum N s theta r /
          ((fixedSet N s).card : ℝ)) ≤
        ∑ r ∈ Ico 1 s,
          (N : ℝ) * (3 : ℝ) ^ (-theta) * R ^ r := by
      apply sum_le_sum
      intro r hr
      have hrBounds := mem_Ico.mp hr
      simpa [R] using
        (fixedReverseTermSum_div_card_le
          (N := N) (s := s) (r := r) (theta := theta)
          htheta hN hs1 hsN hrBounds.1 hrBounds.2)
    _ ≤ ∑' r : ℕ,
        (N : ℝ) * (3 : ℝ) ^ (-theta) * R ^ r := by
      exact hsummable.sum_le_tsum (Ico 1 s)
        (fun r _ => by positivity)
    _ = (N : ℝ) * (3 : ℝ) ^ (-theta) /
        (1 - centralRenyiRatio theta
          (centralSeparatorProportion N s)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1]
      simp only [R]
      field_simp
end CollatzEndpointTransport.FixedTotal
