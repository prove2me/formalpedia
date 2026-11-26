-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_binomialAnnuli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:46:19.093801+00:00
-- url     : https://prove2.me/submissions/ce3e583f-817d-404a-a361-d68e6955f346

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_binomialAnnulus_index
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulus_index_mem_range

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H : ℕ} (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range (H + 1), f k) =
      ∑ j ∈ Finset.range (H + 1), ∑ k ∈ binomialAnnulus H j, f k := by
  classical
  let index := fun k : ℕ =>
    binomialCenterDistance H k / binomialAnnulusWidth H
  have hmaps : ∀ k ∈ Finset.range (H + 1),
      index k ∈ Finset.range (H + 1) := by
    intro k hk
    exact binomialAnnulus_index_mem_range hk
  calc
    (∑ k ∈ Finset.range (H + 1), f k) =
        ∑ j ∈ Finset.range (H + 1),
          ∑ k ∈ Finset.range (H + 1) with index k = j, f k := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps f).symm
    _ = ∑ j ∈ Finset.range (H + 1),
          ∑ k ∈ binomialAnnulus H j, f k := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_filter, binomialAnnulus, index]
        constructor
        · rintro ⟨hk, hindex⟩
          refine ⟨hk, ?_⟩
          have hmem := mem_binomialAnnulus_index hk
          simpa [hindex] using (Finset.mem_filter.mp hmem).2
        · rintro ⟨hk, hkann⟩
          refine ⟨hk, ?_⟩
          exact Nat.div_eq_of_lt_le hkann.1 hkann.2
      · intro k hk
        rfl
end CollatzEndpointTransport.FixedTotal
