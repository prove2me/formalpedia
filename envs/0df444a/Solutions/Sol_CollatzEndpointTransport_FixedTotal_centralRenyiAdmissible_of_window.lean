-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralRenyiAdmissible_of_window
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:33:43.343498+00:00
-- url     : https://prove2.me/submissions/7c0e8395-e684-49d9-915b-b23f4f92a665

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_window_lower
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_window_upper


set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta eta : ℝ}
    (heta0 : 0 < eta) (hetaHalf : eta < 1 / 2)
    (hN : 1 < N)
    (hinterior : (1 / 2 - eta) * N > 1 / 2)
    (hsizePi :
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1))
    (hsizeDrift :
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N)
    (hcen : InCentralRenyiWindow N s eta) :
    CentralRenyiAdmissible N s theta eta := by
  have hlower := central_window_lower hcen
  have hupper := central_window_upper hcen
  have hs1 : 1 < s := by
    have : (1 : ℝ) < s := by linarith
    exact_mod_cast this
  have hsN : s < N := by
    have : (s : ℝ) < N := by linarith
    exact_mod_cast this
  exact ⟨hN, hs1, hsN, hcen, hsizePi, hsizeDrift⟩
end CollatzEndpointTransport.FixedTotal
