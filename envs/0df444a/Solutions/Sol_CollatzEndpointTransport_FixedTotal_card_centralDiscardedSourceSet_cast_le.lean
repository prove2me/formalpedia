-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_centralDiscardedSourceSet_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:40:24.930612+00:00
-- url     : https://prove2.me/submissions/254c41af-f411-4bfb-b152-64a04aff845a

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceParityTail_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceLateFirstOdd_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralDiscardedSourceSet_le

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
    ((centralDiscardedSourceSet M theta eta).card : ℝ) ≤
      ((M + 1) * 2 ^ (M - K) : ℕ) +
        (2 : ℝ) ^ M *
          (2 * Real.exp (-2 * (eta / 4) ^ 2 * M)) := by
  have hcard := card_centralDiscardedSourceSet_le
    hKM heta0 hetaHalf hK hetaM hstartup
  have hlate := card_sourceLateFirstOdd_le hKM
  have htail := card_sourceParityTail_le
    (M := M) (t := eta / 4) (by positivity) (by linarith)
  have hcardR :
      ((centralDiscardedSourceSet M theta eta).card : ℝ) ≤
        (sourceLateFirstOdd M K).card +
          (sourceParityTail M (eta / 4)).card := by
    exact_mod_cast hcard
  calc
    ((centralDiscardedSourceSet M theta eta).card : ℝ) ≤
        (sourceLateFirstOdd M K).card +
          (sourceParityTail M (eta / 4)).card := hcardR
    _ ≤ ((M + 1) * 2 ^ (M - K) : ℕ) +
          ((sourceParityTail M (eta / 4)).card : ℝ) := by
      gcongr
    _ ≤ ((M + 1) * 2 ^ (M - K) : ℕ) +
        (2 : ℝ) ^ M *
          (2 * Real.exp (-2 * (eta / 4) ^ 2 * M)) := by
      gcongr
end CollatzEndpointTransport.FixedTotal
