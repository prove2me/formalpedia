-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseMajorantAverage_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:26.092664+00:00
-- url     : https://prove2.me/submissions/cf75caea-8628-4f6b-895b-cd94fbb1322d

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseNonterminalSum_div_card_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_realReverseMajorant_le_nonterminal_add_two
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
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
    (htheta0 : 0 < theta)
    (hN : 1 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta)
    (hcontract : 3 ^ s ≤ 2 ^ N) :
    fixedReverseMajorantAverage N s theta ≤
      (N : ℝ) * (3 : ℝ) ^ (-theta) /
        (1 - centralRenyiRatio theta
          (centralSeparatorProportion N s)) + 2 := by
  have hcard : 0 < ((fixedSet N s).card : ℝ) := by
    rw [card_fixedSet N s (by omega) (by omega)]
    exact_mod_cast Nat.choose_pos (by omega : s - 1 ≤ N - 1)
  have hpoint :
      (∑ c ∈ fixedSet N s, realReverseMajorant theta c) ≤
        fixedReverseNonterminalSum N s theta +
          2 * ((fixedSet N s).card : ℝ) := by
    calc
      (∑ c ∈ fixedSet N s, realReverseMajorant theta c) ≤
          ∑ c ∈ fixedSet N s,
            ((∑ r ∈ Ico 1 s, realReverseMomentTerm theta c r) + 2) := by
        apply sum_le_sum
        intro c hc
        exact realReverseMajorant_le_nonterminal_add_two
          htheta0.le (by omega) hcontract c hc
      _ = fixedReverseNonterminalSum N s theta +
          2 * ((fixedSet N s).card : ℝ) := by
        simp only [sum_add_distrib, sum_const, card_attach, nsmul_eq_mul]
        unfold fixedReverseNonterminalSum fixedReverseTermSum
        rw [Finset.sum_comm]
        ring
  unfold fixedReverseMajorantAverage
  calc
    (∑ c ∈ fixedSet N s, realReverseMajorant theta c) /
          ((fixedSet N s).card : ℝ) ≤
        (fixedReverseNonterminalSum N s theta +
          2 * ((fixedSet N s).card : ℝ)) /
            ((fixedSet N s).card : ℝ) :=
      div_le_div_of_nonneg_right hpoint hcard.le
    _ = fixedReverseNonterminalSum N s theta /
          ((fixedSet N s).card : ℝ) + 2 := by
      field_simp
    _ ≤ (N : ℝ) * (3 : ℝ) ^ (-theta) /
        (1 - centralRenyiRatio theta
          (centralSeparatorProportion N s)) + 2 := by
      linarith [fixedReverseNonterminalSum_div_card_le
        htheta0 hN hs1 hsN hpiAlpha]
end CollatzEndpointTransport.FixedTotal
