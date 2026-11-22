-- Prove2me | solution 1 for GJKKL.Main.Regime.bnd_first_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:47.198826+00:00
-- url     : https://prove2.me/submissions/54c521bd-8981-4e0d-8bc5-5cbf5ed5e36e

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_x_ge
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Main_Regime_x_le_one
public import Theorems.Thm_GJKKL_Main_Regime_dhat_pos
public import Theorems.Thm_GJKKL_Main_Regime_dhat_le_dx
public import Theorems.Thm_GJKKL_Main_Regime_delta_nonneg
public import Theorems.Thm_GJKKL_Main_Regime_delta_le_half
public import Theorems.Thm_GJKKL_Main_Regime_k_ge


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
theorem _root_.solution {t : ℕ} (ht : t < m) :
    ((k : ℝ) - 1) * (dhat k d a t + delta k ε d a t) ^ 2 /
        (a * pfrac a t * (dhat k d a t - delta k ε d a t)) ≤ 9 / 2 * ((k : ℝ) - 1) * (d / a) := by
  have hx := R.x_pos ha hm ht.le
  have hdh := R.dhat_pos ha hm ht.le
  have hδ0 := R.delta_nonneg ha hm ht.le
  have hδ := R.delta_le_half (R.x_ge ha hm ht.le) (R.x_le_one ha hm t)
  have hdx := R.dhat_le_dx ha hm ht.le
  have hK : 0 ≤ (k : ℝ) - 1 := by linarith [R.k_ge]
  set dh := dhat k d a t
  set δ := delta k ε d a t
  set x := pfrac a t
  have hL : 0 < dh - δ := by linarith
  rw [div_le_iff₀ (mul_pos (mul_pos ha hx) hL)]
  have e : 9 / 2 * ((k : ℝ) - 1) * (d / a) * (a * x * (dh - δ)) =
      9 / 2 * ((k : ℝ) - 1) * (d * x * (dh - δ)) := by
    have ha0 : a ≠ 0 := ha.ne'
    first | (field_simp; ring) | field_simp
  rw [e]
  have h1 : (dh + δ) ^ 2 ≤ 9 / 2 * (dh * (dh - δ)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) (show 0 ≤ 7 * dh + δ by linarith)]
  have h2 : dh * (dh - δ) ≤ d * x * (dh - δ) := mul_le_mul_of_nonneg_right hdx hL.le
  have h3 : (dh + δ) ^ 2 ≤ 9 / 2 * (d * x * (dh - δ)) := by linarith
  have := mul_le_mul_of_nonneg_left h3 hK
  linarith
end GJKKL.Main.Regime
