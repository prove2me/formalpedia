-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.badPrefix_subset_biUnion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:10:23.190968+00:00
-- url     : https://prove2.me/submissions/362712f3-f5aa-4164-90d0-f5c434a8e217

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution (S : Set ℕ) (N : ℕ) :
    badPrefix S N ⊆
      (Finset.range (Nat.log 2 N + 1)).biUnion (shellBad S) := by
  classical
  intro n hn
  rw [badPrefix, Finset.mem_filter, positivePrefix, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, hnN⟩, hnS⟩ := hn
  have hn0 : n ≠ 0 := by omega
  refine Finset.mem_biUnion.2 ⟨Nat.log 2 n, ?_, ?_⟩
  · exact Finset.mem_range.2
      (Nat.lt_succ_of_le (Nat.log_mono_right hnN))
  · rw [shellBad, Finset.mem_filter, dyadicShell, Finset.mem_Ico]
    exact ⟨⟨Nat.pow_log_le_self 2 hn0,
      Nat.lt_pow_succ_log_self (by norm_num) n⟩, hnS⟩
end CollatzEndpointTransport.QuantitativeDensity
