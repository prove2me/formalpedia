-- Prove2me | solution 1 for FirstPassageLinearTransport.fixedSharpEndpointMargin_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:20.37101+00:00
-- url     : https://prove2.me/submissions/cee783a7-547b-4bea-8fb3-d0df657f0623

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEntropyGap_pos
import Theorems.Thm_FirstPassageLinearTransport_timeSupportCriticalExponent_eq_entropy


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {A : ℝ}
    (hA : timeSupportCriticalExponent < A) :
    0 < fixedSharpEndpointMargin A := by
  have hgap := firstPassageEntropyGap_pos
  have hcrit :
      timeSupportCriticalExponent = 1 / (2 * firstPassageEntropyGap) := by
    rw [timeSupportCriticalExponent_eq_entropy]
    rfl
  rw [hcrit] at hA
  unfold fixedSharpEndpointMargin
  have hden : 0 < 2 * firstPassageEntropyGap := by positivity
  have hmul := (div_lt_iff₀ hden).mp hA
  nlinarith
end FirstPassageLinearTransport
