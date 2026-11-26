-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.pow_le_succ_mul_scaledBinomialMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:29.236259+00:00
-- url     : https://prove2.me/submissions/8fed9b3e-7412-414a-bc82-422b6f358ffe

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_scaledBinomialMass_le_mode
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_scaledBinomialMass
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
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {n k : ℕ} (hk : k ≤ n) :
    n ^ n ≤ (n + 1) * scaledBinomialMass n k k := by
  rw [← sum_scaledBinomialMass n k hk]
  calc
    ∑ j ∈ range (n + 1), scaledBinomialMass n k j
        ≤ ∑ _j ∈ range (n + 1), scaledBinomialMass n k k := by
          apply sum_le_sum
          intro j hj
          exact scaledBinomialMass_le_mode hk (Nat.le_of_lt_succ (mem_range.mp hj))
    _ = (n + 1) * scaledBinomialMass n k k := by simp
end CollatzEndpointTransport.FixedTotal
