-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_centralDiscardedSourceSet_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:38:21.127801+00:00
-- url     : https://prove2.me/submissions/d8b89849-111f-4292-b10f-809da756d0a5

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceRealParityTail_subset_sourceParityTail
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralDiscardedSourceSet_subset

set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {M K : ℕ} {theta eta : ℝ}
    (hKM : K ≤ M)
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    (centralDiscardedSourceSet M theta eta).card ≤
      (sourceLateFirstOdd M K).card +
        (sourceParityTail M (eta / 4)).card := by
  have hcover := centralDiscardedSourceSet_subset
    hKM heta0 hetaHalf hK hetaM hstartup
  have hrealTail :
      sourceRealParityTail M (eta / 2) ⊆
        sourceParityTail M (eta / 4) := by
    convert sourceRealParityTail_subset_sourceParityTail
        (M := M) (t := eta / 2) (by positivity) (by linarith) (by linarith)
      using 1 <;> ring
  calc
    (centralDiscardedSourceSet M theta eta).card ≤
        (sourceLateFirstOdd M K ∪
          sourceRealParityTail M (eta / 2)).card :=
      Finset.card_le_card hcover
    _ ≤ (sourceLateFirstOdd M K).card +
          (sourceRealParityTail M (eta / 2)).card :=
      Finset.card_union_le _ _
    _ ≤ (sourceLateFirstOdd M K).card +
          (sourceParityTail M (eta / 4)).card :=
      Nat.add_le_add_left (Finset.card_le_card hrealTail) _
end CollatzEndpointTransport.FixedTotal
