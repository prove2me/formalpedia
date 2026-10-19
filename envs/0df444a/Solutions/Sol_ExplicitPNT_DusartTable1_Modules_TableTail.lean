-- Prove2me | solution 1 for ExplicitPNT.DusartTable1.Modules.TableTail
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-10-18T13:01:04.062339+00:00
-- url     : https://prove2.me/submissions/34b25382-99f4-42ae-8600-3d4bbe4f4746

import Definitions.Def_DusartTable1ZeroRanges_433_20261018
import Theorems.Thm_ExplicitPNT_dusart_refined_psi_error_of_zero_free_region
import Theorems.Thm_ExplicitPNT_kadiri_zero_free_region_569693
import Definitions.Def_DusartThetaTable1Intervals
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1000000
open ExplicitPNT.DusartTable1

namespace ExplicitPNT.DusartTable1

private theorem exponential_decay (u : ℝ) (hu : 50 ≤ u) :
    u * Real.exp (-u) ≤ 50 * Real.exp (-50) := by
  have h := Real.add_one_le_exp (u - 50)
  have hlinear : u ≤ 50 * Real.exp (u - 50) := by linarith
  have hmul := mul_le_mul_of_nonneg_right hlinear (Real.exp_pos (-u)).le
  calc
    u * Real.exp (-u) ≤ 50 * Real.exp (u - 50) * Real.exp (-u) := hmul
    _ = 50 * Real.exp (-50) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf

private theorem exp_fifty_lower : (10 : ℝ) ^ 21 ≤ Real.exp 50 := by
  have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by
    have h := Real.exp_one_gt_d9
    norm_num at h ⊢
    linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27 / 10) he 50
  have hid : (Real.exp (1 : ℝ)) ^ 50 = Real.exp 50 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [hid] at hp
  norm_num at hp ⊢
  linarith

private theorem envelope_tail (u : ℝ) (hu : 50 ≤ u) :
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (1 / 10 ^ 19 : ℝ) := by
  have hpi := Real.pi_gt_three
  have h8 : (8 : ℝ) / Real.pi ≤ 4 := (div_le_iff₀ Real.pi_pos).2 (by linarith)
  have hc : Real.sqrt (8 / Real.pi) ≤ 2 := by
    have h := Real.sqrt_le_sqrt h8
    norm_num at h ⊢
    exact h
  have hs : Real.sqrt u ≤ u := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hdecay := exponential_decay u hu
  have hinv : Real.exp (-50) ≤ 1 / (10 : ℝ) ^ 21 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) exp_fifty_lower
  calc
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u)
      ≤ 2 * u * Real.exp (-u) := by gcongr
    _ = 2 * (u * Real.exp (-u)) := by ring
    _ ≤ 2 * (50 * Real.exp (-50)) := by gcongr
    _ ≤ 2 * (50 * (1 / (10 : ℝ) ^ 21)) := by gcongr
    _ ≤ (1 / 10 ^ 19 : ℝ) := by norm_num

private theorem psi_tail (x : ℝ) (hx : Real.exp 15000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (1 / 10 ^ 19 : ℝ) * x := by
  have hx0 : 0 < x := (Real.exp_pos 15000).trans_le hx
  have hlog : (15000 : ℝ) ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 15000) hx
    simpa only [Real.log_exp] using h
  let R : ℝ := 569693 / 100000
  let X : ℝ := Real.sqrt (Real.log x / R)
  have hR : 0 < R := by norm_num [R]
  have hX : 50 ≤ X := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hR).2
    dsimp [R]
    norm_num at *
    linarith
  have hz : ∀ s : ℂ, 2 * Real.pi < |s.im| →
      1 - 1 / (R * Real.log |s.im|) < s.re → riemannZeta s ≠ 0 := by
    intro s ht hσ
    apply ExplicitPNT.kadiri_zero_free_region_569693 s (by linarith [Real.pi_gt_three])
    exact hσ.le
  have hthreshold : max (836 / 100 : ℝ) (8 / R) < X := by
    apply max_lt
    · linarith
    · have hnum : (8 : ℝ) / R < 50 := by norm_num [R]
      linarith
  have hpsi := ExplicitPNT.dusart_refined_psi_error_of_zero_free_region R hR hz x hx0 hthreshold
  change |Chebyshev.psi x - x| < x * Real.sqrt (8 / Real.pi) * Real.sqrt X *
    Real.exp (-X) * Real.sqrt (Real.sqrt
      (1 - (Real.log (2 * Real.pi) - 1 / 2) / X)) at hpsi
  have hcpos : 0 ≤ Real.log (2 * Real.pi) - 1 / 2 := by
    have hlogpi : (1 : ℝ) < Real.log (2 * Real.pi) := by
      apply (Real.lt_log_iff_exp_lt (by positivity)).2
      have he := Real.exp_one_lt_d9
      have hp := Real.pi_gt_three
      norm_num at he
      linarith
    linarith
  have hf : Real.sqrt (Real.sqrt
      (1 - (Real.log (2 * Real.pi) - 1 / 2) / X)) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    apply Real.sqrt_le_one.mpr
    have hd := div_nonneg hcpos (show 0 ≤ X by linarith)
    linarith
  have hbase := envelope_tail X hX
  apply le_trans hpsi.le
  calc
    x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) *
        Real.sqrt (Real.sqrt (1 - (Real.log (2 * Real.pi) - 1 / 2) / X))
      ≤ x * Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X) * 1 := by
        gcongr
    _ = x * (Real.sqrt (8 / Real.pi) * Real.sqrt X * Real.exp (-X)) := by ring
    _ ≤ x * (1 / 10 ^ 19 : ℝ) := mul_le_mul_of_nonneg_left hbase hx0.le
    _ = _ := by ring

private theorem row_epsilon_lower (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows) :
    (1 / 10 ^ 19 : ℝ) ≤ (r.epsilon : ℝ) := by
  simp only [DusartThetaTable.rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst r <;> norm_num

private theorem all_table_bounds_in_tail
    (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp 15000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x := by
  exact (psi_tail x hx).trans
    (mul_le_mul_of_nonneg_right (row_epsilon_lower r hr)
      ((Real.exp_pos 15000).trans_le hx).le)

end ExplicitPNT.DusartTable1

theorem solution :
(
    ∀ (u : ℝ) (hu : 50 ≤ u),
    u * Real.exp (-u) ≤ 50 * Real.exp (-50)
) ∧
(
    (10 : ℝ) ^ 21 ≤ Real.exp 50
) ∧
(
    ∀ (u : ℝ) (hu : 50 ≤ u),
    Real.sqrt (8 / Real.pi) * Real.sqrt u * Real.exp (-u) ≤
      (1 / 10 ^ 19 : ℝ)
) ∧
(
    ∀ (x : ℝ) (hx : Real.exp 15000 ≤ x),
    |Chebyshev.psi x - x| ≤ (1 / 10 ^ 19 : ℝ) * x
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows),
    (1 / 10 ^ 19 : ℝ) ≤ (r.epsilon : ℝ)
) ∧
(
    ∀ (r : DusartThetaTable.Row) (hr : r ∈ DusartThetaTable.rows)
    (x : ℝ) (hx : Real.exp 15000 ≤ x),
    |Chebyshev.psi x - x| ≤ (r.epsilon : ℝ) * x
) := by
  exact ⟨exponential_decay, exp_fifty_lower, envelope_tail, psi_tail, row_epsilon_lower, all_table_bounds_in_tail⟩
