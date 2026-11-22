-- Prove2me | solution 1 for GJKKL.Main.Regime.x_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:58:41.456473+00:00
-- url     : https://prove2.me/submissions/708a1f3a-16e7-4f0a-b91b-f5a61b16659d

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_x_ge
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos


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
theorem _root_.solution {t : ℕ} (ht : t ≤ m) : 0 < pfrac a t := R.mu_pos.trans_le (R.x_ge ha hm ht)
end GJKKL.Main.Regime
