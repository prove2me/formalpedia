-- Prove2me | solution 1 for FockSPR.rho_pointwise_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:46.411683+00:00
-- url     : https://prove2.me/submissions/997e24a3-d742-4505-9390-546536d8a4d0

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho
public import Theorems.Thm_FockSPR_rho_lipschitz

set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FockSPR
namespace FockSPR
theorem _root_.solution (w z : ℂ) : rho w ≤ rho z + ‖w - z‖ := by
  have h := rho_lipschitz.dist_le_mul w z
  rw [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm] at h
  linarith only [h, le_abs_self (rho w - rho z)]
end FockSPR
