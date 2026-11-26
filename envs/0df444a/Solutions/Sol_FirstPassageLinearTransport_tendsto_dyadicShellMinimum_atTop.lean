-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_dyadicShellMinimum_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:17.43643+00:00
-- url     : https://prove2.me/submissions/6071158a-a245-4546-ac8f-e5042136d6cb

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_le_dyadicShellMinimum
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {U : ℕ → ℝ} (hU : Tendsto U atTop atTop) :
    Tendsto (dyadicShellMinimum U) atTop atTop := by
  rw [tendsto_atTop] at hU ⊢
  intro b
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hU b)
  have hpowT : Tendsto (fun M : ℕ => 2 ^ M) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hpow := (tendsto_atTop.1 hpowT) N
  filter_upwards [hpow] with M hMN
  apply le_dyadicShellMinimum U M
  intro n hn
  exact hN n (hMN.trans (mem_dyadicShell.mp hn).1)
end FirstPassageLinearTransport
