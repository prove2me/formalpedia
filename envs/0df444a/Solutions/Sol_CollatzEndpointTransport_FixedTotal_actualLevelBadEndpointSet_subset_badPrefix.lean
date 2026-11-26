-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelBadEndpointSet_subset_badPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:34:38.338827+00:00
-- url     : https://prove2.me/submissions/29881d4c-6497-4bde-b276-5b5066cc6513

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_lt_three_pow_succ
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpoint_pos


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Set ℕ) (M s : ℕ) :
    actualLevelBadEndpointSet S M s ⊆
      QuantitativeDensity.badPrefix S (3 ^ (s + 1)) := by
  classical
  intro y hy
  rw [actualLevelBadEndpointSet, Finset.mem_filter] at hy
  rcases Finset.mem_image.mp hy.1 with ⟨x, hx, hxy⟩
  have hsx : sourceCodeOddCount x = s :=
    (Finset.mem_filter.mp hx).2
  have hyPos : 0 < y := by
    rw [← hxy]
    exact sourceEndpoint_pos x
  have hyLt : y < 3 ^ (s + 1) := by
    rw [← hxy]
    exact sourceEndpoint_lt_three_pow_succ hsx
  rw [QuantitativeDensity.badPrefix, Finset.mem_filter,
    QuantitativeDensity.positivePrefix, Finset.mem_Icc]
  exact ⟨⟨hyPos, hyLt.le⟩, hy.2⟩
end CollatzEndpointTransport.FixedTotal
