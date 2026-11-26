-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.realReverseMajorant_le_nonterminal_add_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:36.099049+00:00
-- url     : https://prove2.me/submissions/c6d08ba2-1d83-4625-9b39-c5f1d1add87d

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_natPow_rpow_eq_rpow_natPow
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_realReverseMajorant_eq_series
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_rpow_nat_div_rpow_nat_le_one
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
    (htheta : 0 ≤ theta) (hs0 : 0 < s)
    (hcontract : 3 ^ s ≤ 2 ^ N)
    (c : Composition N) (hc : c ∈ fixedSet N s) :
    realReverseMajorant theta c ≤
      (∑ r ∈ Ico 1 s, realReverseMomentTerm theta c r) + 2 := by
  have hseries := realReverseMajorant_eq_series theta c hc
  have hspend : reverseSpend c s = N := by
    have hlen : c.length = s := (Finset.mem_filter.mp hc).2
    simp [reverseSpend, terminalBlocks, hlen, c.blocks_sum]
  have hpowSmall : 3 ^ (s - 1) ≤ 2 ^ N := by
    exact (pow_le_pow_right₀ (by norm_num : 1 ≤ (3 : ℕ)) (Nat.sub_le s 1)).trans
      hcontract
  have hlast : realReverseMomentTerm theta c s ≤ 1 := by
    unfold realReverseMomentTerm
    rw [hspend,
      ← natPow_rpow_eq_rpow_natPow (by norm_num : (0 : ℝ) ≤ 3)]
    simpa [Nat.cast_pow] using
      (rpow_nat_div_rpow_nat_le_one htheta (by positivity) hpowSmall)
  have htail :
      (((3 : ℝ) ^ theta) ^ s /
        (((2 : ℝ) ^ N) ^ theta)) ≤ 1 := by
    rw [← natPow_rpow_eq_rpow_natPow (by norm_num : (0 : ℝ) ≤ 3)]
    simpa [Nat.cast_pow] using
      (rpow_nat_div_rpow_nat_le_one htheta (by positivity) hcontract)
  rw [hseries, Nat.Ico_succ_right_eq_insert_Ico (by omega : 1 ≤ s),
    sum_insert (by simp)]
  linarith
end CollatzEndpointTransport.FixedTotal
