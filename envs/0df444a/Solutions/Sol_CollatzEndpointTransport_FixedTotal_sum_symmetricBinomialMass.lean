-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_symmetricBinomialMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:10.276438+00:00
-- url     : https://prove2.me/submissions/9236ef96-2ad8-49a6-a38c-1944d4ea4c42

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (H : ℕ) :
    ∑ k ∈ Finset.range (H + 1), symmetricBinomialMass H k = 1 := by
  unfold symmetricBinomialMass
  rw [← Finset.sum_div]
  have hsum :
      (∑ k ∈ Finset.range (H + 1), (H.choose k : ℝ)) = (2 : ℝ) ^ H := by
    exact_mod_cast Nat.sum_range_choose H
  rw [hsum]
  field_simp
end CollatzEndpointTransport.FixedTotal
