-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_stretchedHeightShellAllowance_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:56:42.829195+00:00
-- url     : https://prove2.me/submissions/4eaf5d90-61c2-4bd3-9b06-808713aa79a4

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {zeta alpha : ℝ} (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    Tendsto (stretchedHeightShellAllowance zeta alpha) atTop atTop := by
  have hscale : Tendsto (fun M : ℕ => (M : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const
      (Real.log_pos (by norm_num))
  have hpow : Tendsto
      (fun M : ℕ => (((M : ℝ) * Real.log 2) ^ alpha)) atTop atTop :=
    (tendsto_rpow_atTop halpha).comp hscale
  have hmul : Tendsto
      (fun M : ℕ => zeta * (((M : ℝ) * Real.log 2) ^ alpha)) atTop atTop :=
    hpow.const_mul_atTop hzeta
  change Tendsto
    (fun M : ℕ => Real.exp (zeta * (((M : ℝ) * Real.log 2) ^ alpha)))
      atTop atTop
  exact Real.tendsto_exp_atTop.comp hmul
end FirstPassageLinearTransport
