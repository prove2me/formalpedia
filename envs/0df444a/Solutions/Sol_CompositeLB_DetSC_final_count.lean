-- Prove2me | solution 1 for CompositeLB.DetSC.final_count
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T01:42:36.082752+00:00
-- url     : https://prove2.me/submissions/f3b97865-465b-4d8f-a29a-3709ed462e05

import Mathlib
import Definitions.Def_CompositeLB_DetSC_HardInstance

open CompositeLB.DetSC in
theorem solution (m : ℕ) (hm : 2 ≤ m)
    (lam eps eps0 Q : ℝ)
    (hlam : 0 < lam) (hlam73 : lam < 1 / 73)
    (heps : 0 < eps) (heps0 : 3 * eps / lam < eps0)
    (hQ : Q = bigQ m lam) :
    (m : ℝ) / 2 *
        (Nat.floor ((Real.sqrt Q - 1) / 4 *
          Real.log (eps0 / (2 * Real.sqrt Q * eps))) : ℝ) ≥
      (m : ℝ) / (40 * Real.sqrt lam) *
        Real.log (eps0 / (2 * Real.sqrt Q * eps)) ∧
    (m : ℝ) / (40 * Real.sqrt lam) *
        Real.log (eps0 / (2 * Real.sqrt Q * eps)) ≥
      (m : ℝ) / (40 * Real.sqrt lam) *
        Real.log (Real.sqrt lam * eps0 / (2 * eps)) := by
  set r := Real.sqrt lam with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hlam
  have hlr : lam = r ^ 2 := (Real.sq_sqrt hlam.le).symm
  have hr1 : r < 2 / 17 := by
    rw [hlr] at hlam73
    nlinarith
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  -- bounds on k = ⌊m/2⌋/m
  set k : ℝ := (((m / 2 : ℕ) : ℝ) / (m : ℝ)) with hk
  have hk1 : (1 : ℝ) / 3 ≤ k := by
    rw [hk, div_le_div_iff₀ (by norm_num) (by linarith)]
    have : m ≤ 3 * (m / 2) := by omega
    have : (m : ℝ) ≤ 3 * ((m / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hk2 : k ≤ 1 / 2 := by
    rw [hk, div_le_div_iff₀ (by linarith) (by norm_num)]
    have : 2 * (m / 2) ≤ m := Nat.mul_div_le m 2
    have : 2 * ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
    linarith
  have hinvl : 1 < 1 / lam := by rw [lt_div_iff₀ hlam]; linarith
  have hQe : Q = k * (1 / lam - 1) + 1 := by rw [hQ]; unfold bigQ; rfl
  have hQge : 1 / (3 * lam) + 2 / 3 ≤ Q := by
    rw [hQe]
    have : (1 : ℝ) / 3 * (1 / lam - 1) ≤ k * (1 / lam - 1) :=
      mul_le_mul_of_nonneg_right hk1 (by linarith)
    have e : 1 / (3 * lam) = 1 / 3 * (1 / lam) := by field_simp
    rw [e]; linarith
  have hQle : Q ≤ 1 / lam := by
    rw [hQe]
    have : k * (1 / lam - 1) ≤ 1 / 2 * (1 / lam - 1) :=
      mul_le_mul_of_nonneg_right hk2 (by linarith)
    linarith
  have hQpos : 0 < Q := by
    have : 0 < 1 / (3 * lam) := by positivity
    linarith
  set s := Real.sqrt Q with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hQpos
  have hsle : s ≤ 1 / r := by
    have h1 : s ≤ Real.sqrt (1 / lam) := Real.sqrt_le_sqrt hQle
    rw [hlr, Real.sqrt_div' 1 (sq_nonneg r), Real.sqrt_one, Real.sqrt_sq hr0.le] at h1
    exact h1
  have hs1 : 1 + 2 / (5 * r) ≤ s := by
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    refine le_trans ?_ hQge
    rw [hlr]
    rw [show (1 + 2 / (5 * r)) ^ 2 = (5 * r + 2) ^ 2 / (25 * r ^ 2) by field_simp <;> norm_num,
      show 1 / (3 * r ^ 2) + 2 / 3 = (25 * (1 + 2 * r ^ 2) / 3) / (25 * r ^ 2) by
        field_simp <;> ring]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  set A := eps0 / (2 * s * eps) with hA
  have hA1 : eps0 * r / (2 * eps) ≤ A := by
    rw [hA]
    have : 2 * s * eps ≤ 2 * eps / r := by
      rw [le_div_iff₀ hr0]
      have := mul_le_mul_of_nonneg_left hsle (by linarith : (0 : ℝ) ≤ 2 * eps)
      have e : 2 * eps * (1 / r) * r = 2 * eps := by field_simp
      nlinarith
    have heps0pos : 0 < eps0 := lt_trans (by positivity) heps0
    calc eps0 * r / (2 * eps) = eps0 / (2 * eps / r) := by field_simp
      _ ≤ eps0 / (2 * s * eps) := div_le_div_of_nonneg_left heps0pos.le (by positivity) this
  have hA2 : 3 / (2 * r) < eps0 * r / (2 * eps) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    rw [hlr, div_lt_iff₀ (by positivity)] at heps0
    nlinarith
  have hApos : 0 < A := lt_trans (by positivity : (0 : ℝ) < 3 / (2 * r)) (hA2.trans_le hA1)
  have hr3 : (51 : ℝ) / 4 < 3 / (2 * r) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hexp2 : Real.exp 2 < 51 / 4 := by
    have h1 := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]
    have h0 := Real.exp_pos 1
    nlinarith
  set L := Real.log A with hL
  have hL2 : 2 < L := by
    rw [hL, Real.lt_log_iff_exp_lt hApos]
    linarith
  set y := (s - 1) / 4 * L with hy
  have hsm1 : 2 / (5 * r) ≤ s - 1 := by linarith
  have h17 : (17 : ℝ) / 5 < 2 / (5 * r) := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hy1 : 1 ≤ y := by
    rw [hy]
    have : 17 / 5 < s - 1 := by linarith
    nlinarith
  have hfl : y ≤ 2 * (Nat.floor y : ℝ) := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : (1 : ℝ) ≤ (Nat.floor y : ℝ) := by
      have : 1 ≤ Nat.floor y := Nat.le_floor (by exact_mod_cast hy1)
      exact_mod_cast this
    linarith
  constructor
  · -- main bound
    have hmpos : (0 : ℝ) < m := by linarith
    have e : (m : ℝ) / (40 * r) * L = (m : ℝ) / 2 * ((2 / (5 * r)) / 4 * L / 2) := by
      field_simp <;> ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hL0 : 0 ≤ L := by linarith
    calc (2 / (5 * r)) / 4 * L / 2 ≤ (s - 1) / 4 * L / 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right hsm1 (by norm_num)) hL0) (by norm_num)
      _ = y / 2 := by rw [hy]
      _ ≤ (Nat.floor y : ℝ) := by linarith
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hL]
    have he0 : 0 < eps0 := lt_trans (by positivity) heps0
    apply Real.log_le_log (by positivity)
    rw [mul_comm r eps0]
    exact hA1
