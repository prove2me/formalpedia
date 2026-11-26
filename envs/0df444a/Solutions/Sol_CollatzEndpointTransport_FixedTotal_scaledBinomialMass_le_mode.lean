-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.scaledBinomialMass_le_mode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:41.939561+00:00
-- url     : https://prove2.me/submissions/d0c9df37-9d32-4202-8636-71ece7397cb0

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_scaledBinomialMass_le_succ_of_lt_mean
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_scaledBinomialMass_succ_le_of_mean_le
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
    {n k j : ℕ} (hk : k ≤ n) (hj : j ≤ n) :
    scaledBinomialMass n k j ≤ scaledBinomialMass n k k := by
  by_cases hk0 : k = 0
  · subst k
    by_cases hj0 : j = 0
    · subst j
      rfl
    · simp [scaledBinomialMass, hj0]
  by_cases hknEq : k = n
  · subst k
    rcases lt_or_eq_of_le hj with hjn | rfl
    · have hsub : 0 < n - j := Nat.sub_pos_of_lt hjn
      simp [scaledBinomialMass, Nat.zero_pow hsub]
    · rfl
  have hkn : k < n := lt_of_le_of_ne hk hknEq
  rcases le_total j k with hjk | hkj
  · have hwalk : ∀ d : ℕ, j + d ≤ k →
        scaledBinomialMass n k j ≤ scaledBinomialMass n k (j + d) := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
          intro hd
          have hd' : j + d ≤ k := by omega
          exact (ih hd').trans
            (scaledBinomialMass_le_succ_of_lt_mean hkn (by omega))
    simpa [Nat.add_sub_of_le hjk] using hwalk (k - j) (by omega)
  · have hwalk : ∀ d : ℕ, k + d ≤ j →
        scaledBinomialMass n k (k + d) ≤ scaledBinomialMass n k k := by
      intro d
      induction d with
      | zero => simp
      | succ d ih =>
          intro hd
          have hd' : k + d ≤ j := by omega
          exact (scaledBinomialMass_succ_le_of_mean_le
            (n := n) (k := k) (j := k + d)
            (by omega) (by omega)).trans (ih hd')
    simpa [Nat.add_sub_of_le hkj] using hwalk (j - k) (by omega)
end CollatzEndpointTransport.FixedTotal
