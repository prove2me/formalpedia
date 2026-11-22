-- Prove2me | solution 1 for GJKKL.Main.Regime.dhat_le_dx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:52.107801+00:00
-- url     : https://prove2.me/submissions/f21708ea-91f9-4b5c-b978-5afb373e2673

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Main_Regime_x_le_one
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
theorem _root_.solution {t : ℕ} (ht : t ≤ m) : dhat k d a t ≤ d * pfrac a t := by
  unfold dhat
  have hk1 : k - 1 ≠ 0 := by have := R.two_le; omega
  exact mul_le_mul_of_nonneg_left
    (pow_le_of_le_one (R.x_pos ha hm ht).le (R.x_le_one ha hm t) hk1) R.d_pos.le
end GJKKL.Main.Regime
