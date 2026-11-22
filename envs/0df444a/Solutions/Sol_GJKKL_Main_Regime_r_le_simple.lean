-- Prove2me | solution 1 for GJKKL.Main.Regime.r_le_simple
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:33.548808+00:00
-- url     : https://prove2.me/submissions/f2c0e44c-86cd-4bf0-9a9b-7884949d52b3

module
public import Definitions.Def_GJKKL_Main_Parameters
public import Definitions.Def_GJKKL_Main_TrackParams
public import Theorems.Thm_GJKKL_Main_Regime_x_ge
public import Theorems.Thm_GJKKL_Main_Regime_x_pos
public import Theorems.Thm_GJKKL_Main_Regime_x_le_one
public import Theorems.Thm_GJKKL_Main_Regime_E_pos
public import Theorems.Thm_GJKKL_Main_Regime_d_pos
public import Theorems.Thm_GJKKL_Main_Regime_mu_pos
public import Theorems.Thm_GJKKL_Main_Regime_two_E_le
public import Theorems.Thm_GJKKL_Trajectory_inv_pow_sub_inv_pow_le
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
    delta k ε d a (t + 1) - delta k ε d a t ≤ (Bn k : ℝ) * (d / a) / 2 := by
  have hx := R.x_pos ha hm ht.le
  have hy := R.x_pos ha hm (Nat.succ_le_of_lt ht)
  have hyx := pfrac_succ_le a ha.le t
  have hμy := R.x_ge ha hm (Nat.succ_le_of_lt ht)
  have hμx := R.x_ge ha hm ht.le
  have h := inv_pow_sub_inv_pow_le hy hyx (Bn k)
  rw [pfrac_sub_succ a t] at h
  unfold delta
  set x := pfrac a t
  set y := pfrac a (t + 1)
  -- `2E ≤ µ d y^{B+k-1} ≤ d x y^B`
  have h2E := R.two_E_le hμy (R.x_le_one ha hm (t + 1))
  have hyk : y ^ (k - 1) ≤ 1 := pow_le_one₀ hy.le (R.x_le_one ha hm (t + 1))
  have hE : 2 * d ^ (1 - ε / 8) ≤ d * x * y ^ Bn k := by
    rw [pow_add] at h2E
    have hyB : 0 ≤ y ^ Bn k := pow_nonneg hy.le _
    have h1 : d ^ (-(ε ^ 3)) * d * (y ^ Bn k * y ^ (k - 1)) ≤ d ^ (-(ε ^ 3)) * d * y ^ Bn k := by
      have h0 := mul_le_mul_of_nonneg_left hyk hyB
      have := mul_le_mul_of_nonneg_left h0 (mul_nonneg R.mu_pos.le R.d_pos.le)
      linarith
    have h2 : d ^ (-(ε ^ 3)) * d * y ^ Bn k ≤ x * d * y ^ Bn k := by
      have := mul_le_mul_of_nonneg_right hμx (mul_nonneg R.d_pos.le hyB)
      linarith
    linarith
  have e : d ^ (1 - ε / 8) / y ^ Bn k - d ^ (1 - ε / 8) / x ^ Bn k =
      d ^ (1 - ε / 8) * (1 / y ^ Bn k - 1 / x ^ Bn k) := by ring
  rw [e]
  have h3 := mul_le_mul_of_nonneg_left h R.E_pos.le
  refine h3.trans ?_
  -- `E · B (1/a) / (x y^B) ≤ B d / (2a)`
  have hxyB : 0 < x * y ^ Bn k := mul_pos hx (pow_pos hy _)
  rw [show d ^ (1 - ε / 8) * ((Bn k : ℝ) * (1 / a) / (x * y ^ Bn k)) =
      (Bn k : ℝ) * (1 / a) * (d ^ (1 - ε / 8) / (x * y ^ Bn k)) by ring]
  have hq : d ^ (1 - ε / 8) / (x * y ^ Bn k) ≤ d / 2 := by
    rw [div_le_iff₀ hxyB]; linarith
  have hB : 0 ≤ (Bn k : ℝ) * (1 / a) := by positivity
  calc (Bn k : ℝ) * (1 / a) * (d ^ (1 - ε / 8) / (x * y ^ Bn k)) ≤
        (Bn k : ℝ) * (1 / a) * (d / 2) := mul_le_mul_of_nonneg_left hq hB
    _ = (Bn k : ℝ) * (d / a) / 2 := by ring
end GJKKL.Main.Regime
