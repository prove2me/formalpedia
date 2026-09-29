-- Prove2me | solution 1 for BanditAlgorithm.adversarial_bandit_exp3ix_high_probability_regret_tuned
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-07-20T20:58:25.693891+00:00
-- url     : https://prove2.me/submissions/9acbe8b5-0e17-44a4-814e-58b6834b12bb

import Theorems.Thm_BanditAlgorithm_adversarial_bandit_exp3ix_master_high_probability_regret
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ)
    (hη : η = Real.sqrt ((Real.log k + Real.log ((k + 1) / δ)) / (n * k)))
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3IXPolicy η (η / 2) π) :
    BanditAlgorithm.adversarialMeasure x π n
      {h : BanditAlgorithm.BanditHistory k n |
        2 * Real.sqrt ((2 * Real.log (k + 1) + Real.log (1 / δ)) * (n * k)) +
          Real.log ((k + 1) / δ) ≤ BanditAlgorithm.adversarialRandomRegret n x h} ≤
      ENNReal.ofReal δ := by
  subst η
  have hk0 : 0 < (k : ℝ) := by positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  have hklog : 0 < Real.log (k : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hk
  have hL : 0 < Real.log (((k : ℝ) + 1) / δ) := by
    apply Real.log_pos
    have hδ1 := hδ.2
    have hkp : (1 : ℝ) < k + 1 := by
      have hkR : (1 : ℝ) < k := by exact_mod_cast hk
      linarith
    apply lt_of_lt_of_le hkp
    exact (le_div_iff₀ hδ.1).2 (by nlinarith)
  have heta :
      0 < Real.sqrt ((Real.log (k : ℝ) + Real.log (((k : ℝ) + 1) / δ)) /
        ((n : ℝ) * k)) := by positivity
  have hmaster :=
    BanditAlgorithm.adversarial_bandit_exp3ix_master_high_probability_regret
      hk n hn x hx δ hδ _ heta π hπ
  apply le_trans (measure_mono ?_) hmaster
  intro h hh
  try dsimp only [Set.mem_setOf_eq] at hh ⊢
  let N : ℝ := (n : ℝ) * k
  let a : ℝ := Real.log ((k : ℝ) + 1)
  let ell : ℝ := Real.log (1 / δ)
  let L : ℝ := Real.log (((k : ℝ) + 1) / δ)
  let B : ℝ := Real.log (k : ℝ) + L
  let C : ℝ := 2 * a + ell
  let e : ℝ := Real.sqrt (B / N)
  have hN : 0 < N := by dsimp [N]; positivity
  have hB : 0 < B := by dsimp [B, L]; linarith
  have he : 0 < e := by dsimp [e]; positivity
  have he_sq : e ^ 2 = B / N := by
    dsimp [e]
    rw [Real.sq_sqrt]
    positivity
  have hBe : B / e = e * N := by
    have he0 : e ≠ 0 := ne_of_gt he
    have hN0 : N ≠ 0 := ne_of_gt hN
    field_simp [he0, hN0] at he_sq ⊢
    nlinarith
  have hroot : e * N = Real.sqrt (B * N) := by
    symm
    apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (mul_pos he hN)).2
    have hN0 : N ≠ 0 := ne_of_gt hN
    field_simp [hN0] at he_sq ⊢
    nlinarith
  have hlogdiv : L = a + ell := by
    dsimp [L, a, ell]
    rw [Real.log_div (by positivity) (ne_of_gt hδ.1)]
    rw [Real.log_div one_ne_zero (ne_of_gt hδ.1)]
    simp only [Real.log_one, zero_sub]
    ring
  have hlogk : Real.log (k : ℝ) ≤ a := by
    dsimp [a]
    apply Real.log_le_log
    · positivity
    · norm_num
  have hBC : B ≤ C := by
    dsimp [B, C]
    rw [hlogdiv]
    linarith
  have hBN : B * N ≤ C * N := mul_le_mul_of_nonneg_right hBC hN.le
  have hsqrt : Real.sqrt (B * N) ≤ Real.sqrt (C * N) := Real.sqrt_le_sqrt hBN
  have hbound :
      Real.log (k : ℝ) / e + e * N + (1 + 1 / e) * L ≤
        2 * Real.sqrt (C * N) + L := by
    have he0 : e ≠ 0 := ne_of_gt he
    calc
      Real.log (k : ℝ) / e + e * N + (1 + 1 / e) * L
          = e * N + B / e + L := by dsimp [B]; field_simp [he0]; ring
      _ = 2 * Real.sqrt (B * N) + L := by rw [hBe, hroot]; ring
      _ ≤ 2 * Real.sqrt (C * N) + L := by gcongr
  dsimp [e, B, L, C, ell, a, N] at hbound
  apply le_trans hbound
  simpa [mul_assoc] using hh
