-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_sourceParityTail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:35:30.427283+00:00
-- url     : https://prove2.me/submissions/d240a6ed-c08d-4345-8ddd-9763e0501649

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceParityTail_eq
import Theorems.Thm_CollatzEndpointTransport_Terras_card_shellParityPrefixBadAt_le


set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (htHalf : t ≤ 1 / 2) :
    ((sourceParityTail M t).card : ℝ) ≤
      (2 : ℝ) ^ M * (2 * Real.exp (-2 * t ^ 2 * M)) := by
  rw [card_sourceParityTail_eq]
  exact Terras.card_shellParityPrefixBadAt_le (le_refl M) ht0 htHalf
end CollatzEndpointTransport.FixedTotal
