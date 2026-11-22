-- Prove2me | solution 1 for GJKKL.Main.Regime.g_le_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:21:39.981801+00:00
-- url     : https://prove2.me/submissions/78f4e8cf-b9e8-47e6-a07f-ce94749802dd

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_cast_k_sub_two
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Main_Regime_dhat_le_dx
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_k_ge
public import Theorems.Thm_GJKKL_Main_g_le_aux
public import Theorems.Thm_GJKKL_Trajectory_pfrac_sub_succ
public import Theorems.Thm_GJKKL_Trajectory_pfrac_succ_le


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
    dhat k d a t - dhat k d a (t + 1) ≤ ((k : ℝ) - 1) * (d / a) := by
  have hx := R.x_pos ha hm ht.le
  have hy := R.x_pos ha hm (Nat.succ_le_of_lt ht)
  have hyx := pfrac_succ_le a ha.le t
  have hk' : k - 1 = (k - 2) + 1 := by have := R.two_le; omega
  have hc : (k : ℝ) - 1 = ((k - 2 : ℕ) : ℝ) + 1 := by rw [cast_k_sub_two R.two_le]; ring
  have h := g_le_aux (k - 2) hy.le hyx hx ha R.d_pos.le (pfrac_sub_succ a t)
  rw [← hk', ← hc] at h
  unfold dhat
  refine h.trans ?_
  -- `(k-1) d x^{k-1} / (a x) ≤ (k-1) d / a`
  have hle := R.dhat_le_dx ha hm ht.le
  unfold dhat at hle
  have hK : 0 ≤ (k : ℝ) - 1 := by linarith [R.k_ge]
  rw [div_le_iff₀ (mul_pos ha hx)]
  have : ((k : ℝ) - 1) * (d / a) * (a * pfrac a t) = ((k : ℝ) - 1) * (d * pfrac a t) := by
    have ha0 : a ≠ 0 := ha.ne'
    first | (field_simp; ring) | field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_left hle hK
end GJKKL.Main.Regime
