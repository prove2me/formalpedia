-- Prove2me | solution 1 for FockSPR.rho_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:33.130179+00:00
-- url     : https://prove2.me/submissions/f65a0460-6ca3-4cc5-86f7-285fa04e3e1e

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Theorems.Thm_FockSPR_rho_pointwise_upper

set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FockSPR
namespace FockSPR
theorem _root_.solution (w : ℂ) : rho w ≤ ‖w‖ := by
  simpa only [rho, add_zero, norm_one, sub_self, abs_zero, zero_add, sub_zero] using
    rho_pointwise_upper w 0
end FockSPR
