-- Prove2me | solution 1 for GJKKL.Main.le_rpow_of_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:04.708702+00:00
-- url     : https://prove2.me/submissions/00dcc074-2250-4a50-b1f7-7dcac67c4d80

module
public import Definitions.Def_GJKKL_Main_TrackParams
public import Definitions.Def_GJKKL_Numerics_Final
public import Definitions.Def_GJKKL_Main_Theorem

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory GJKKL.History GJKKL.Numerics
namespace GJKKL.Main
theorem _root_.solution {K x d : ℝ} (hK : 0 ≤ K) (hx : 0 < x) (hd : K ^ (1 / x) ≤ d) :
    K ≤ d ^ x := by
  have h1 : (K ^ (1 / x)) ^ x = K := by
    rw [← rpow_mul hK, one_div_mul_cancel hx.ne', rpow_one]
  calc K = (K ^ (1 / x)) ^ x := h1.symm
    _ ≤ d ^ x := rpow_le_rpow (rpow_nonneg hK _) hd hx.le
end GJKKL.Main
