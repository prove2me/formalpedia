-- Prove2me | solution 1 for DetANN.theorem_1_1_parameters
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:14:42.714381+00:00
-- url     : https://prove2.me/submissions/bf081fbe-f35b-49d1-8096-c4e9b651a901

import Mathlib
import Definitions.Def_DetANN_Multigraph

open DetANN in
theorem solution (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 ≤ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊ ∧
    theta0 ^ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊ ≤ ε / 200 ∧
    (theta0 ^ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊) ^ 2 /
        (1 - (theta0 ^ ⌈Real.logb (1 / theta0) (200 / ε)⌉₊) ^ 2) ≤ ε ^ 2 / 10 ^ 4 ∧
    ((1 + ε / 100) + Real.sqrt (2 * (1 + ε / 100) ^ 2 * (ε ^ 2 / 10 ^ 4) +
        12 * (ε ^ 2 / 10 ^ 6) * (1 + (1 + ε / 100)) ^ 2)) /
      Real.sqrt (1 - ε ^ 2 / 10 ^ 6) ≤ 1 + ε := by
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hθpos : 0 < theta0 := by unfold theta0; positivity
  have hθ1 : theta0 < 1 := by unfold theta0; nlinarith
  have hb : 1 < 1 / theta0 := by rw [lt_div_iff₀ hθpos]; linarith
  have hx : 1 < 200 / ε := by rw [lt_div_iff₀ hε0]; linarith
  have hlog : 0 < Real.logb (1 / theta0) (200 / ε) := Real.logb_pos hb hx
  obtain ⟨N, hN⟩ : ∃ N, N = ⌈Real.logb (1 / theta0) (200 / ε)⌉₊ := ⟨_, rfl⟩
  rw [← hN]
  have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_ceil_iff.mpr hlog
  have hNge : Real.logb (1 / theta0) (200 / ε) ≤ N := by rw [hN]; exact Nat.le_ceil _
  have hpow : theta0 ^ N ≤ ε / 200 := by
    rw [← Real.rpow_natCast]
    have h1 := Real.rpow_le_rpow_of_exponent_ge hθpos hθ1.le hNge
    obtain ⟨L, hL⟩ : ∃ L, L = Real.logb (1 / theta0) (200 / ε) := ⟨_, rfl⟩
    rw [← hL] at h1
    have hinv : (1 / theta0) ^ L = 200 / ε := by
      rw [hL]; exact Real.rpow_logb (by positivity) hb.ne' (by positivity)
    have h3 : theta0 ^ L = ((1 / theta0) ^ L)⁻¹ := by
      rw [← Real.inv_rpow (by positivity), one_div, inv_inv]
    have h2 : theta0 ^ L = ε / 200 := by
      rw [h3, hinv, inv_div]
    linarith
  have ha0 : 0 ≤ theta0 ^ N := by positivity
  refine ⟨hN1, hpow, ?_, ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, a = theta0 ^ N := ⟨_, rfl⟩
    rw [← ha] at hpow ha0 ⊢
    have ha2 : a ^ 2 ≤ ε ^ 2 / 40000 := by
      have := mul_le_mul hpow hpow ha0 (by positivity)
      nlinarith
    have hden : 3 / 4 ≤ 1 - a ^ 2 := by nlinarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  · obtain ⟨u, hu⟩ : ∃ u, u = ε := ⟨_, rfl⟩
    rw [← hu]
    rw [← hu] at hε0 hε1
    have hbr : 2 * (1 + u / 100) ^ 2 / 10 ^ 4 + 12 * (2 + u / 100) ^ 2 / 10 ^ 6 ≤ 1 / 2500 := by
      nlinarith
    have hin : 2 * (1 + u / 100) ^ 2 * (u ^ 2 / 10 ^ 4) +
        12 * (u ^ 2 / 10 ^ 6) * (1 + (1 + u / 100)) ^ 2 ≤ (u / 50) ^ 2 := by
      have e : 2 * (1 + u / 100) ^ 2 * (u ^ 2 / 10 ^ 4) +
          12 * (u ^ 2 / 10 ^ 6) * (1 + (1 + u / 100)) ^ 2 =
          u ^ 2 * (2 * (1 + u / 100) ^ 2 / 10 ^ 4 + 12 * (2 + u / 100) ^ 2 / 10 ^ 6) := by ring
      rw [e]
      have : u ^ 2 * (2 * (1 + u / 100) ^ 2 / 10 ^ 4 + 12 * (2 + u / 100) ^ 2 / 10 ^ 6) ≤
          u ^ 2 * (1 / 2500) := mul_le_mul_of_nonneg_left hbr (by positivity)
      nlinarith
    have hS : Real.sqrt (2 * (1 + u / 100) ^ 2 * (u ^ 2 / 10 ^ 4) +
        12 * (u ^ 2 / 10 ^ 6) * (1 + (1 + u / 100)) ^ 2) ≤ u / 50 := by
      calc _ ≤ Real.sqrt ((u / 50) ^ 2) := Real.sqrt_le_sqrt hin
        _ = u / 50 := Real.sqrt_sq (by positivity)
    have hz0 : 0 ≤ 1 - u ^ 2 / 10 ^ 6 := by nlinarith
    have hz1 : 1 - u ^ 2 / 10 ^ 6 ≤ 1 := by nlinarith
    have hT : 1 - u ^ 2 / 10 ^ 6 ≤ Real.sqrt (1 - u ^ 2 / 10 ^ 6) := by
      rw [Real.le_sqrt hz0 hz0]
      nlinarith
    have hTpos : 0 < Real.sqrt (1 - u ^ 2 / 10 ^ 6) := by
      apply Real.sqrt_pos.mpr; nlinarith
    rw [div_le_iff₀ hTpos]
    have h1 : (1 + u) * (1 - u ^ 2 / 10 ^ 6) ≤ (1 + u) * Real.sqrt (1 - u ^ 2 / 10 ^ 6) :=
      mul_le_mul_of_nonneg_left hT (by linarith)
    nlinarith
