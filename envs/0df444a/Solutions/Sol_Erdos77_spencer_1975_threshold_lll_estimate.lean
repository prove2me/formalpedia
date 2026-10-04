-- Prove2me | solution 1 for Erdos77.spencer_1975_threshold_lll_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:39:53.640399+00:00
-- url     : https://prove2.me/submissions/0c989a43-4973-420f-b53a-b947585560f5

import Mathlib

open Filter

theorem Erdos77_a4_rpow_half (k : ℕ) : (2 : ℝ) ^ ((k : ℝ) / 2) = (Real.sqrt 2) ^ k := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

theorem Erdos77_a4_choose_two (j : ℕ) : 2 * (j + 2).choose 2 = j + (j + 2) * j + 2 := by
  have h := Nat.choose_two_right (j + 2)
  have h1 : (j + 2 - 1) = j + 1 := by omega
  rw [h1] at h
  have he : 2 ∣ (j + 2) * (j + 1) := by
    rw [mul_comm]
    exact (Nat.even_mul_succ_self (j + 1)).two_dvd
  rw [h, Nat.mul_div_cancel' he]
  ring

theorem Erdos77_a4_bound (c : ℝ) (hc0 : 0 < c) (j : ℕ) :
    (4 : ℝ) * ((j + 2).choose 2 : ℝ) *
      (Nat.choose (Nat.floor (c * (Real.sqrt 2 / Real.exp 1) * ((j + 2 : ℕ) : ℝ) *
          (2 : ℝ) ^ (((j + 2 : ℕ) : ℝ) / 2)) - 2) j : ℝ) *
      (2 : ℝ) ^ (1 - ((j + 2).choose 2 : ℝ))
    ≤ 2 * Real.exp 2 * (((j : ℝ) + 2) * ((j : ℝ) + 1)) * c ^ j := by
  rw [Erdos77_a4_rpow_half]
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  set s := Real.sqrt 2 with hsdef
  set e := Real.exp 1 with hedef
  set X := c * (s / e) * ((j + 2 : ℕ) : ℝ) * s ^ (j + 2) with hXdef
  have hX0 : 0 ≤ X := by positivity
  set m := Nat.floor X - 2 with hm
  have hmX : (m : ℝ) ≤ X := le_trans (Nat.cast_le.mpr (Nat.sub_le _ _)) (Nat.floor_le hX0)
  have hB1 : ((m.choose j : ℕ) : ℝ) ≤ (m : ℝ) ^ j / (j.factorial : ℝ) := Nat.choose_le_pow_div j m
  have hB2 : (m : ℝ) ^ j / (j.factorial : ℝ) ≤ X ^ j / (j.factorial : ℝ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hmX j
  have hfac : ((j : ℝ) + 2) ^ j / (j.factorial : ℝ) ≤ Real.exp ((j : ℝ) + 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) j
  have hexp : Real.exp ((j : ℝ) + 2) = e ^ j * Real.exp 2 := by
    rw [Real.exp_add, hedef, ← Real.exp_nat_mul]; ring_nf
  have hXj : X ^ j / (j.factorial : ℝ)
      = (c * s / e) ^ j * s ^ ((j + 2) * j) * (((j : ℝ) + 2) ^ j / (j.factorial : ℝ)) := by
    have hXj0 : X ^ j = (c * s / e) ^ j * s ^ ((j + 2) * j) * ((j : ℝ) + 2) ^ j := by
      rw [hXdef, pow_mul]; push_cast; rw [← mul_pow, ← mul_pow]; congr 1; ring
    rw [hXj0, mul_div_assoc]
  have hB3 : X ^ j / (j.factorial : ℝ) ≤ c ^ j * s ^ j * s ^ ((j + 2) * j) * Real.exp 2 := by
    rw [hXj]
    calc (c * s / e) ^ j * s ^ ((j + 2) * j) * (((j : ℝ) + 2) ^ j / (j.factorial : ℝ))
        ≤ (c * s / e) ^ j * s ^ ((j + 2) * j) * (e ^ j * Real.exp 2) := by
          apply mul_le_mul_of_nonneg_left (hfac.trans hexp.le) (by positivity)
      _ = c ^ j * s ^ j * s ^ ((j + 2) * j) * Real.exp 2 := by
          rw [div_pow, mul_pow]; field_simp
  have hC : (2 : ℝ) * ((j + 2).choose 2 : ℝ) = ((j : ℝ) + 2) * ((j : ℝ) + 1) := by
    have h' : ((2 * (j + 2).choose 2 : ℕ) : ℝ) = ((j + (j + 2) * j + 2 : ℕ) : ℝ) := by
      rw [Erdos77_a4_choose_two]
    push_cast at h'
    rw [h']; ring
  have hP : (2 : ℝ) ^ ((j + 2).choose 2) = s ^ j * s ^ ((j + 2) * j) * 2 := by
    calc (2 : ℝ) ^ ((j + 2).choose 2) = (s ^ 2) ^ ((j + 2).choose 2) := by rw [hs2]
      _ = s ^ (2 * (j + 2).choose 2) := by rw [← pow_mul]
      _ = s ^ (j + (j + 2) * j + 2) := by rw [Erdos77_a4_choose_two]
      _ = s ^ j * s ^ ((j + 2) * j) * s ^ 2 := by rw [pow_add, pow_add]
      _ = s ^ j * s ^ ((j + 2) * j) * 2 := by rw [hs2]
  have hrp : (2 : ℝ) ^ (1 - ((j + 2).choose 2 : ℝ)) = 2 / (2 : ℝ) ^ ((j + 2).choose 2) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
  rw [hrp, hP]
  have hB : ((m.choose j : ℕ) : ℝ) ≤ c ^ j * s ^ j * s ^ ((j + 2) * j) * Real.exp 2 :=
    hB1.trans (hB2.trans hB3)
  have hCn : (0 : ℝ) ≤ 4 * ((j + 2).choose 2 : ℝ) := by positivity
  have hQ : (0 : ℝ) ≤ 2 / (s ^ j * s ^ ((j + 2) * j) * 2) := by positivity
  calc 4 * ((j + 2).choose 2 : ℝ) * ((m.choose j : ℕ) : ℝ) * (2 / (s ^ j * s ^ ((j + 2) * j) * 2))
      ≤ 4 * ((j + 2).choose 2 : ℝ) * (c ^ j * s ^ j * s ^ ((j + 2) * j) * Real.exp 2)
          * (2 / (s ^ j * s ^ ((j + 2) * j) * 2)) := by
        apply mul_le_mul_of_nonneg_right _ hQ
        exact mul_le_mul_of_nonneg_left hB hCn
    _ = 2 * Real.exp 2 * (2 * ((j + 2).choose 2 : ℝ)) * c ^ j := by
        field_simp
        ring
    _ = 2 * Real.exp 2 * (((j : ℝ) + 2) * ((j : ℝ) + 1)) * c ^ j := by rw [hC]

theorem solution (epsilon : Real) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    Filter.Eventually (fun k : Nat =>
        (4 : Real) * (Nat.choose k 2 : Real) *
            (Nat.choose
              (Nat.floor
                ((1 - epsilon) * (Real.sqrt 2 / Real.exp 1) * (k : Real) *
                  (2 : Real) ^ ((k : Real) / 2)) - 2)
              (k - 2) : Real) *
            (2 : Real) ^ (1 - (Nat.choose k 2 : Real)) < 1) Filter.atTop := by
  have hc0 : 0 < 1 - epsilon := by linarith
  have habs : |1 - epsilon| < 1 := by rw [abs_of_pos hc0]; linarith
  have t2 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 habs
  have t1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 habs
  have t0 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 0 habs
  have hT : Tendsto (fun j : ℕ => 2 * Real.exp 2 * (((j : ℝ) + 2) * ((j : ℝ) + 1)) * (1 - epsilon) ^ j)
      atTop (nhds 0) := by
    have h := ((t2.add (t1.const_mul 3)).add (t0.const_mul 2)).const_mul (2 * Real.exp 2)
    rw [show (2 * Real.exp 2) * ((0 + 3 * 0) + 2 * 0 : ℝ) = 0 by ring] at h
    refine h.congr (fun j => ?_)
    simp only [pow_zero, pow_one]
    ring
  have hev := hT.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  rw [eventually_atTop] at hev ⊢
  obtain ⟨N, hN⟩ := hev
  refine ⟨N + 2, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hj : N ≤ j := by omega
  rw [Nat.add_sub_cancel]
  exact lt_of_le_of_lt (Erdos77_a4_bound (1 - epsilon) hc0 j) (hN j hj)
