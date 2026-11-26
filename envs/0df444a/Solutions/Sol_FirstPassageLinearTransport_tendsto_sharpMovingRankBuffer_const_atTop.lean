-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_sharpMovingRankBuffer_const_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:31:58.772223+00:00
-- url     : https://prove2.me/submissions/9baf4cc0-10d8-4f93-80ac-fe01132ed6cf

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointNaturalDensity
import Definitions.Def_FirstPassageLinearTransport_PolylogExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Theorems.Thm_FirstPassageLinearTransport_fixedSharpEndpointMargin_pos
import Theorems.Thm_FirstPassageLinearTransport_sharpMovingRankBuffer_const_ge

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℝ} (hA : timeSupportCriticalExponent < A) :
    Tendsto (sharpMovingRankBuffer (fun _ => A)) atTop atTop := by
  have hq : 0 < fixedSharpEndpointMargin A :=
    fixedSharpEndpointMargin_pos hA
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop
  have hlogT : Tendsto
      (fun M : ℕ => Real.logb 2 ((M : ℝ) + 2)) atTop atTop :=
    Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2) |>.comp hxT
  have hlowerT : Tendsto
      (fun M : ℕ => fixedSharpEndpointMargin A *
        Real.logb 2 ((M : ℝ) + 2)) atTop atTop :=
    hlogT.const_mul_atTop hq
  rw [tendsto_atTop] at hlowerT ⊢
  intro B
  filter_upwards [hlowerT B] with M hM
  exact hM.trans (sharpMovingRankBuffer_const_ge A M)
end FirstPassageLinearTransport
