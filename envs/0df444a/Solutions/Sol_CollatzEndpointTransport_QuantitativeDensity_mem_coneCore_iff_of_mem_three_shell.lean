-- Prove2me | solution 1 for CollatzEndpointTransport.QuantitativeDensity.mem_coneCore_iff_of_mem_three_shell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:56:39.959797+00:00
-- url     : https://prove2.me/submissions/c52a22b0-8919-4c58-99cd-1d59bc6db0c5

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
import Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_card_positivePrefix
attribute [local simp] CollatzEndpointTransport.QuantitativeDensity.card_positivePrefix



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.QuantitativeDensity
theorem _root_.solution
    {K j n : ℕ} {eta : ℝ} {S : Set ℕ}
    (hn : 3 ^ j ≤ n ∧ n < 3 ^ (j + 1)) :
    n ∈ coneCore K eta S ↔
      0 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ eta * j →
        ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S := by
  have hnlog : Nat.log 3 n = j :=
    Nat.log_eq_of_pow_le_of_lt_pow hn.1 hn.2
  simp only [coneCore, Set.mem_setOf_eq, hnlog]
end CollatzEndpointTransport.QuantitativeDensity
