-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_sharpMovingRankBuffer_criticalMultiplierExponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:32:54.848268+00:00
-- url     : https://prove2.me/submissions/7b1a2603-98ca-47f1-926c-eeacd6129080

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_tendsto_clippedCriticalMultiplier_atTop
import Theorems.Thm_FirstPassageLinearTransport_sharpMovingRankBuffer_criticalMultiplierExponent_ge
import Theorems.Thm_FirstPassageLinearTransport_firstPassageEntropyGap_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {U : ℕ → ℝ} (hUpos : ∀ n, 0 < U n)
    (hU : Tendsto U atTop atTop) :
    Tendsto (sharpMovingRankBuffer (criticalMultiplierExponent U))
      atTop atTop := by
  have hwT := tendsto_clippedCriticalMultiplier_atTop hU
  have hlogT : Tendsto
      (fun M => Real.logb 2 (clippedCriticalMultiplier U M)) atTop atTop :=
    Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2) |>.comp hwT
  have hlowerT : Tendsto
      (fun M => firstPassageEntropyGap *
        Real.logb 2 (clippedCriticalMultiplier U M)) atTop atTop :=
    hlogT.const_mul_atTop firstPassageEntropyGap_pos
  rw [tendsto_atTop] at hlowerT ⊢
  intro B
  filter_upwards [hlowerT B] with M hM
  exact hM.trans
    (sharpMovingRankBuffer_criticalMultiplierExponent_ge hUpos M)
end FirstPassageLinearTransport
