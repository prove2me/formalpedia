-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.card_badPrefix_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:12:49.395255+00:00
-- url     : https://prove2.me/submissions/7affb4d4-afa4-4690-9d2a-b7d38362d171

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_badPrefix_subset_biUnion

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution (S : Set ℕ) (N : ℕ) :
    (badPrefix S N).card ≤
      ∑ M ∈ Finset.range (Nat.log 2 N + 1), (shellBad S M).card := by
  classical
  calc
    (badPrefix S N).card
        ≤ ((Finset.range (Nat.log 2 N + 1)).biUnion (shellBad S)).card :=
      Finset.card_le_card (badPrefix_subset_biUnion S N)
    _ ≤ ∑ M ∈ Finset.range (Nat.log 2 N + 1), (shellBad S M).card :=
      Finset.card_biUnion_le
end CollatzEndpointTransport.QuantitativeDensity
