-- Prove2me | solution 1 for Erdos77.spencer_1975_threshold_eventual_size
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:33:44.269874+00:00
-- url     : https://prove2.me/submissions/b1f8ad25-161b-4215-9c82-67b24279f1a9

import Mathlib

open Filter

theorem Erdos77_aux_pow_tendsto :
    Tendsto (fun k : ℕ => (2 : ℝ) ^ ((k : ℝ) / 2)) atTop atTop := by
  have h : (fun k : ℕ => (2 : ℝ) ^ ((k : ℝ) / 2)) = fun k : ℕ => (Real.sqrt 2) ^ k := by
    funext k
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [h]
  apply tendsto_pow_atTop_atTop_of_one_lt
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

open Filter in
theorem solution (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Eventually (fun k : Nat =>
      2 <= k /\
        k <= Nat.floor
          ((1 - epsilon) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
            (2 : Real) ^ ((k : Real) / 2))) Filter.atTop := by
  set c : ℝ := (1 - epsilon) * (Real.sqrt 2 / Real.exp 1) with hcdef
  have hc : 0 < c := by
    apply mul_pos (by linarith)
    exact div_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.exp_pos 1)
  have h1 : ∀ᶠ k : ℕ in atTop, 1 / c ≤ (2 : ℝ) ^ ((k : ℝ) / 2) :=
    Erdos77_aux_pow_tendsto.eventually_ge_atTop (1 / c)
  filter_upwards [h1, eventually_ge_atTop 2] with k hk hk2
  refine ⟨hk2, ?_⟩
  apply Nat.le_floor
  have hkpos : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hcp : 1 ≤ c * (2 : ℝ) ^ ((k : ℝ) / 2) := by
    rw [div_le_iff₀' hc] at hk
    linarith
  calc (k : ℝ) = (k : ℝ) * 1 := by ring
    _ ≤ (k : ℝ) * (c * (2 : ℝ) ^ ((k : ℝ) / 2)) := mul_le_mul_of_nonneg_left hcp hkpos
    _ = c * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 2) := by ring
