-- Prove2me | solution 1 for GJKKL.Main.cast_k_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:56:22.273468+00:00
-- url     : https://prove2.me/submissions/5ad28adc-9f68-434a-8cae-98f70b49ca0c

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
namespace GJKKL.Main
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) : ((k - 2 : ℕ) : ℝ) = (k : ℝ) - 2 := by
  rw [Nat.cast_sub hk]; norm_num
end GJKKL.Main
