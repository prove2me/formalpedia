-- Prove2me | solution 1 for BanditAlgorithm.adversarial_bandit_exp3ix_high_probability_regret
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-07-20T20:51:36.810409+00:00
-- url     : https://prove2.me/submissions/defc664c-3beb-41ee-bf63-d3f396bf069e

import Theorems.Thm_BanditAlgorithm_adversarial_bandit_exp3ix_master_high_probability_regret
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory

theorem solution
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : η = Real.sqrt (2 * Real.log (k + 1) / (n * k)))
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3IXPolicy η (η / 2) π) :
    BanditAlgorithm.adversarialMeasure x π n
      {h : BanditAlgorithm.BanditHistory k n |
        Real.sqrt (8 * n * k * Real.log (k + 1)) +
          Real.sqrt (n * k / (2 * Real.log (k + 1))) * Real.log (1 / δ) +
          Real.log ((k + 1) / δ) ≤ BanditAlgorithm.adversarialRandomRegret n x h} ≤
      ENNReal.ofReal δ := by
  subst η
  have hk0 : 0 < (k : ℝ) := by positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  have hN : 0 < (n : ℝ) * k := mul_pos hn0 hk0
  have hk1 : (1 : ℝ) < k + 1 := by
    have hkR : (1 : ℝ) < k := by exact_mod_cast hk
    norm_num at hkR ⊢
    linarith
  have ha : 0 < Real.log ((k : ℝ) + 1) := Real.log_pos hk1
  have heta : 0 < Real.sqrt (2 * Real.log ((k : ℝ) + 1) / ((n : ℝ) * k)) := by
    positivity
  have hmaster :=
    BanditAlgorithm.adversarial_bandit_exp3ix_master_high_probability_regret
      hk n hn x hx δ hδ _ heta π hπ
  apply le_trans (measure_mono ?_) hmaster
  intro h hh
  try dsimp only [Set.mem_setOf_eq] at hh ⊢
  let a : ℝ := Real.log ((k : ℝ) + 1)
  let N : ℝ := (n : ℝ) * k
  let e : ℝ := Real.sqrt (2 * a / N)
  have ha' : 0 < a := by simpa [a] using ha
  have hN' : 0 < N := by simpa [N] using hN
  have he : 0 < e := by simpa [e, a, N] using heta
  have he_sq : e ^ 2 = 2 * a / N := by
    dsimp [e]
    rw [Real.sq_sqrt]
    positivity
  have hrootN : e * N = Real.sqrt (2 * a * N) := by
    symm
    apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (mul_pos he hN')).2
    have hN0 : N ≠ 0 := ne_of_gt hN'
    field_simp [hN0] at he_sq ⊢
    nlinarith
  have hinv : 1 / e = Real.sqrt (N / (2 * a)) := by
    symm
    apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity : 0 < 1 / e)).2
    have he0 : e ≠ 0 := ne_of_gt he
    have ha0 : a ≠ 0 := ne_of_gt ha'
    have hN0 : N ≠ 0 := ne_of_gt hN'
    field_simp [he0, ha0, hN0] at he_sq ⊢
    nlinarith
  have hsqrt8 : 2 * (e * N) = Real.sqrt (8 * N * a) := by
    symm
    apply (Real.sqrt_eq_iff_mul_self_eq_of_pos (by positivity : 0 < 2 * (e * N))).2
    rw [mul_assoc]
    nlinarith [show (e * N) * (e * N) = 2 * a * N by
      rw [hrootN, Real.mul_self_sqrt]
      positivity]
  have hlogk : Real.log (k : ℝ) ≤ a := by
    dsimp [a]
    apply Real.log_le_log
    · positivity
    · norm_num
  have hlogdiv : Real.log (((k : ℝ) + 1) / δ) = a + Real.log (1 / δ) := by
    rw [Real.log_div (by positivity) (ne_of_gt hδ.1)]
    rw [Real.log_div one_ne_zero (ne_of_gt hδ.1)]
    simp only [Real.log_one, zero_sub]
    dsimp [a]
    ring
  have htwoa : 2 * a / e = e * N := by
    have he0 : e ≠ 0 := ne_of_gt he
    have hN0 : N ≠ 0 := ne_of_gt hN'
    field_simp [he0, hN0] at he_sq ⊢
    nlinarith
  have ha_over : a / e = e * N / 2 := by
    calc
      a / e = (2 * a / e) / 2 := by ring
      _ = e * N / 2 := by rw [htwoa]
  have hinva : (1 / e) * a = e * N / 2 := by
    rw [one_div, inv_mul_eq_div, ha_over]
  have hbound :
      Real.log (k : ℝ) / e + e * N +
          (1 + 1 / e) * Real.log (((k : ℝ) + 1) / δ) ≤
        Real.sqrt (8 * N * a) +
          Real.sqrt (N / (2 * a)) * Real.log (1 / δ) +
          Real.log (((k : ℝ) + 1) / δ) := by
    rw [hlogdiv, hinv]
    have he0 : 0 < e := he
    calc
      Real.log (k : ℝ) / e + e * N +
            (1 + Real.sqrt (N / (2 * a))) * (a + Real.log (1 / δ))
          ≤ a / e + e * N +
            (1 + Real.sqrt (N / (2 * a))) * (a + Real.log (1 / δ)) := by
              gcongr
      _ = Real.sqrt (8 * N * a) +
            Real.sqrt (N / (2 * a)) * Real.log (1 / δ) +
            (a + Real.log (1 / δ)) := by
              rw [← hinv, ← hsqrt8, ha_over]
              calc
                e * N / 2 + e * N + (1 + 1 / e) * (a + Real.log (1 / δ)) =
                    e * N / 2 + e * N + (a + Real.log (1 / δ)) +
                      (1 / e) * a + (1 / e) * Real.log (1 / δ) := by ring
                _ = 2 * (e * N) + (1 / e) * Real.log (1 / δ) +
                      (a + Real.log (1 / δ)) := by rw [hinva]; ring
  dsimp [e, N, a] at hbound
  apply le_trans hbound
  simpa [mul_assoc] using hh
