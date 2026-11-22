-- Prove2me | solution 1 for GJKKL.Main.Regime.dhat_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:23.469177+00:00
-- url     : https://prove2.me/submissions/2b11ca45-191a-47c1-8563-535cdbcdc6ea

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Main_Regime_d_pos


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
theorem _root_.solution {t : ℕ} (ht : t ≤ m) : 0 < dhat k d a t :=
  mul_pos R.d_pos (pow_pos (R.x_pos ha hm ht) _)
end GJKKL.Main.Regime
