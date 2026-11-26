-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_clippedShellHeight_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:25.058807+00:00
-- url     : https://prove2.me/submissions/4e9b4d1d-7489-44ed-98a1-7af509ff20fe

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_tendsto_dyadicShellMinimum_atTop

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {R : ℕ → ℝ} (hR : Tendsto R atTop atTop) :
    Tendsto (clippedShellHeight R) atTop atTop := by
  have hleft := tendsto_dyadicShellMinimum_atTop hR
  have hright : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  rw [tendsto_atTop] at hleft hright ⊢
  intro b
  filter_upwards [hleft b, hright b] with M hL hR
  exact le_min hL hR
end FirstPassageLinearTransport
