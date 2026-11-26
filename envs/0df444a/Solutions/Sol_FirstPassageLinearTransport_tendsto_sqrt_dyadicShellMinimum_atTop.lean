-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_sqrt_dyadicShellMinimum_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:24.38436+00:00
-- url     : https://prove2.me/submissions/be86b4ce-f799-43ac-8c9d-571808cea7fd

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
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    Tendsto (fun M => Real.sqrt (dyadicShellMinimum U M)) atTop atTop := by
  have hminT := tendsto_dyadicShellMinimum_atTop hU
  rw [tendsto_atTop] at hminT ⊢
  intro b
  let b₀ := max b 0
  have hb₀ : 0 ≤ b₀ := le_max_right _ _
  have hlarge := hminT (b₀ ^ 2)
  filter_upwards [hlarge] with M hM
  have hmin0 : 0 ≤ dyadicShellMinimum U M :=
    (sq_nonneg b₀).trans hM
  have hsqrtSq := Real.sq_sqrt hmin0
  have hsqrt0 := Real.sqrt_nonneg (dyadicShellMinimum U M)
  have hb : b ≤ b₀ := le_max_left _ _
  nlinarith
end FirstPassageLinearTransport
