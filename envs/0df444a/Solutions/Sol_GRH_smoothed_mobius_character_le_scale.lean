-- Prove2me | solution 1 for GRH.smoothed_mobius_character_le_scale
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T23:58:58.037899+00:00
-- url     : https://prove2.me/submissions/a78f7170-d5ec-4efa-8ef8-3e26889f90ba

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open OAI.ShortDraftMellin

theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (D : ℝ)
    (hD : 0 < D) : ‖mobiusExpSum χ D⁻¹‖ ≤ D := by
  let r := Real.exp (-D⁻¹)
  have hrpos : 0 < r := Real.exp_pos _
  have hrone : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (inv_pos.mpr hD))
  let F (n : ℕ) : ℂ := χ n * (ArithmeticFunction.moebius n : ℂ) *
    Real.exp (-(n : ℝ) * D⁻¹)
  have hterm (n : ℕ) : ‖F n‖ ≤ r ^ n := by
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    have hc : ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [norm_mul]
      simpa using mul_le_mul (χ.norm_le_one _) hμ (norm_nonneg _) zero_le_one
    have he : Real.exp (-(n : ℝ) * D⁻¹) = r ^ n := by
      simpa [r, neg_mul, mul_neg] using Real.exp_nat_mul (-D⁻¹) n
    dsimp only [F]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), he]
    simpa using mul_le_mul_of_nonneg_right hc (pow_nonneg hrpos.le n)
  have hg := hasSum_geometric_of_lt_one hrpos.le hrone
  have hn : Summable (fun n => ‖F n‖) :=
    hg.summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
  have hF0 : F 0 = 0 := by simp [F]
  have htail := ((summable_nat_add_iff 1).mpr hn).tsum_le_tsum
    (fun n => hterm (n + 1)) ((summable_nat_add_iff 1).mpr hg.summable)
  have hnormsum := hn.tsum_eq_zero_add
  have hgeomsum := hg.summable.tsum_eq_zero_add
  simp only [hF0, norm_zero, zero_add] at hnormsum
  rw [hg.tsum_eq, pow_zero] at hgeomsum
  have hmass : (∑' n, ‖F n‖) ≤ (1-r)⁻¹ - 1 := by linarith
  have hprod : r * (D⁻¹ + 1) ≤ 1 := calc
    _ ≤ r * Real.exp D⁻¹ := mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) hrpos.le
    _ = 1 := by dsimp [r]; rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne']
  have hrD : r * (1 + D) ≤ D := calc
    _ = (r * (D⁻¹ + 1)) * D := by field_simp [hD.ne']
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hprod hD.le
    _ = D := one_mul D
  have hcap : (1-r)⁻¹ ≤ D+1 := by
    apply (inv_le_iff_one_le_mul₀ (sub_pos.mpr hrone)).mpr
    nlinarith only [hrD]
  change ‖∑' n, F n‖ ≤ D
  exact (norm_tsum_le_tsum_norm hn).trans (hmass.trans (by linarith only [hcap]))
