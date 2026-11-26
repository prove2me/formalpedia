-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_shellRankRpow_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:02.841115+00:00
-- url     : https://prove2.me/submissions/9d4889da-bcf1-42b1-bf23-02309c793fff

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {N : ℝ} (hN : 0 < N) :
    Tendsto (fun M : ℕ => ((M : ℝ) + 2) ^ N) atTop atTop := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  exact (tendsto_rpow_atTop hN).comp hxT
end FirstPassageLinearTransport
