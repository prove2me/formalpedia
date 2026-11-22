-- Prove2me | solution 1 for GJKKL.Main.Regime.x_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:14.495581+00:00
-- url     : https://prove2.me/submissions/ef04cc53-bcc3-4518-964d-f6e42acbecbe

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Trajectory_pfrac_le_one


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
open GJKKL.Main.Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
variable {a : ℝ} {m : ℕ} (ha : 0 < a) (hm : (m : ℝ) ≤ (1 - d ^ (-(ε ^ 3))) * a)
include ha hm
namespace GJKKL.Main.Regime
theorem _root_.solution (t : ℕ) : pfrac a t ≤ 1 := pfrac_le_one ha.le t
end GJKKL.Main.Regime
