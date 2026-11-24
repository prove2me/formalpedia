-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.thetaDOneWord_eq_series
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:24:41.254582+00:00
-- url     : https://prove2.me/submissions/789a818e-59ce-4f40-872a-c358c6236ddf

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
import Theorems.Thm_DyckAlgebra_DyckRepU_theta_y1_dps


set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
namespace DyckAlgebra.DyckRepU
theorem _root_.solution : ρ.thetaDOneWord = ρ.dPositiveSeries := by
  unfold thetaDOneWord dPositiveSeries
  calc
    ρ.dm * -ρ.Θy1 * ρ.Θdps = -ρ.dm * (ρ.Θy1 * ρ.Θdps) := by noncomm_ring
    _ = -ρ.dm * (ρ.w 1 * ρ.yy 1 * ρ.dps) := by rw [ρ.theta_y1_dps]
    _ = ρ.dm * ρ.w 1 * -ρ.yy 1 * ρ.dps := by noncomm_ring
end DyckAlgebra.DyckRepU
