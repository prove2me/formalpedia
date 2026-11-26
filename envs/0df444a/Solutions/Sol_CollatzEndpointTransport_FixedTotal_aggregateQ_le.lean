-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.aggregateQ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:40:22.811626+00:00
-- url     : https://prove2.me/submissions/27336188-2a95-479f-ae8f-a8ae93a32298

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedTotal_firstMoment_exact
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
    (N : ℕ) (hN : 0 < N) :
    (∑ s ∈ Finset.Icc 1 N,
        ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) ≤
      4 * N * 4 ^ (N - 1) := by
  have hpartition :
      (∑ s ∈ Finset.Icc 1 N,
          ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) =
        ∑ c : Composition N, (3 ^ c.length + syracuseNumerator c) := by
    have hmap :
        ∀ c ∈ (Finset.univ : Finset (Composition N)),
          c.length ∈ Finset.Icc 1 N := by
      intro c hc
      exact Finset.mem_Icc.mpr
        ⟨c.length_pos_of_pos hN, c.length_le⟩
    calc
      (∑ s ∈ Finset.Icc 1 N,
          ∑ c ∈ fixedSet N s, (3 ^ s + syracuseNumerator c)) =
          ∑ s ∈ Finset.Icc 1 N,
            ∑ c ∈ fixedSet N s,
              (3 ^ c.length + syracuseNumerator c) := by
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro c hc
        have hlen : c.length = s := (Finset.mem_filter.mp hc).2
        rw [hlen]
      _ = ∑ c : Composition N,
          (3 ^ c.length + syracuseNumerator c) := by
        simpa [fixedSet] using
          (Finset.sum_fiberwise_of_maps_to
            (s := (Finset.univ : Finset (Composition N)))
            (t := Finset.Icc 1 N)
            (g := fun c : Composition N => c.length)
            hmap (fun c => 3 ^ c.length + syracuseNumerator c))
  rw [hpartition]
  let Q := ∑ c : Composition N, (3 ^ c.length + syracuseNumerator c)
  have hExact : 2 * Q = (N + 7) * 4 ^ (N - 1) := by
    exact fixedTotal_firstMoment_exact N hN
  have hN7 : N + 7 ≤ 8 * N := by omega
  have hscaled :=
    Nat.mul_le_mul_right (4 ^ (N - 1)) hN7
  have htwo : 2 * Q ≤ 2 * (4 * N * 4 ^ (N - 1)) := by
    rw [hExact]
    nlinarith
  exact Nat.le_of_mul_le_mul_left htwo (by norm_num)
end CollatzEndpointTransport.FixedTotal
