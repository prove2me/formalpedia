-- Prove2me | solution 1 for FockSPR.rho_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:29.362105+00:00
-- url     : https://prove2.me/submissions/d82c182e-b530-404a-8103-1b237b0bb278

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LipschitzRho

set_option autoImplicit true
@[expose] public section
public section
open Complex Real
open FockSPR
namespace FockSPR
theorem _root_.solution : LipschitzWith 1 rho := by
  apply LipschitzWith.mk_one
  intro w z
  simp only [rho, dist_eq_norm]
  calc |( |‖(1 : ℂ) + w‖ - 1| ) - ( |‖(1 : ℂ) + z‖ - 1| )|
      ≤ |(‖(1 : ℂ) + w‖ - 1) - (‖(1 : ℂ) + z‖ - 1)| :=
        abs_abs_sub_abs_le_abs_sub _ _
    _ = |‖(1 : ℂ) + w‖ - ‖(1 : ℂ) + z‖| := by ring_nf
    _ ≤ ‖(1 : ℂ) + w - ((1 : ℂ) + z)‖ := abs_norm_sub_norm_le _ _
    _ = ‖w - z‖ := by ring_nf
end FockSPR
