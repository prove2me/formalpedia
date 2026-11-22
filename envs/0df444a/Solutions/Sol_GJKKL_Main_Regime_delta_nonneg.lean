-- Prove2me | solution 1 for GJKKL.Main.Regime.delta_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:00:26.363034+00:00
-- url     : https://prove2.me/submissions/c3ff52a5-3cb0-4344-85a3-20582ed5fb22

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Main_Regime_E_pos


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
theorem _root_.solution {t : ℕ} (ht : t ≤ m) : 0 ≤ delta k ε d a t :=
  div_nonneg R.E_pos.le (pow_nonneg (R.x_pos ha hm ht).le _)
end GJKKL.Main.Regime
