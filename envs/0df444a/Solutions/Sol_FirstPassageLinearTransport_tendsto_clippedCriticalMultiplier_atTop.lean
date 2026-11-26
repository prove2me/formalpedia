-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_clippedCriticalMultiplier_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:44.977134+00:00
-- url     : https://prove2.me/submissions/4d8d7899-8661-4490-a163-d59b5f25387c

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_tendsto_sqrt_dyadicShellMinimum_atTop

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    Tendsto (clippedCriticalMultiplier U) atTop atTop := by
  have hleft := tendsto_sqrt_dyadicShellMinimum_atTop hU
  have hright : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  rw [tendsto_atTop] at hleft hright ⊢
  intro b
  filter_upwards [hleft b, hright b] with M hL hR
  exact le_min hL hR
end FirstPassageLinearTransport
