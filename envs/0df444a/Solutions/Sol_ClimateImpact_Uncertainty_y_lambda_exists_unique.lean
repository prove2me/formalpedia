-- Prove2me | solution 1 for ClimateImpact.Uncertainty.y_lambda_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:26:51.680807+00:00
-- url     : https://prove2.me/submissions/72c25aa2-64f0-4a07-8992-79e887229aa7

import Mathlib
import Definitions.Def_ClimateImpact_Uncertainty_Portfolio

set_option autoImplicit false
open Matrix ClimateImpact.Uncertainty

lemma clu2_core (k s b : ℝ) (hk : 0 < k) (hb : 0 ≤ b) :
    ∃! y : ℝ, 0 < y ∧ y = Real.exp (-k * (s + b * y)) := by
  let H : ℝ → ℝ := fun y => Real.log y + k * (s + b * y)
  have hequiv : ∀ y : ℝ, 0 < y → (y = Real.exp (-k * (s + b * y)) ↔ H y = 0) := by
    intro y hy
    constructor
    · intro h
      have := congrArg Real.log h
      rw [Real.log_exp] at this
      simp only [H]; linarith
    · intro h
      have : Real.log y = -k * (s + b * y) := by simp only [H] at h; linarith
      rw [← this, Real.exp_log hy]
  have hmono : StrictMonoOn H (Set.Ioi 0) := by
    intro x hx y hy hxy
    simp only [H]
    have h1 := Real.log_lt_log hx hxy
    have h2 : b * x ≤ b * y := mul_le_mul_of_nonneg_left hxy.le hb
    have h3 := mul_le_mul_of_nonneg_left h2 hk.le
    nlinarith
  set y1 : ℝ := Real.exp (-(|k * s| + k * b + 1)) with hy1
  set y2 : ℝ := Real.exp (|k * s| + 1) with hy2
  have hy1pos : 0 < y1 := Real.exp_pos _
  have hy2pos : 0 < y2 := Real.exp_pos _
  have hy1le : y1 ≤ 1 := by
    rw [hy1, Real.exp_le_one_iff]
    have := abs_nonneg (k * s)
    have : 0 ≤ k * b := mul_nonneg hk.le hb
    linarith
  have hy21 : 1 ≤ y2 := by
    rw [hy2]; apply Real.one_le_exp; have := abs_nonneg (k * s); linarith
  have hH1 : H y1 < 0 := by
    simp only [H]
    rw [hy1, Real.log_exp]
    have h1 : b * y1 ≤ b * 1 := mul_le_mul_of_nonneg_left hy1le hb
    have h2 := mul_le_mul_of_nonneg_left h1 hk.le
    have h3 := le_abs_self (k * s)
    nlinarith
  have hH2 : 0 < H y2 := by
    simp only [H]
    rw [hy2, Real.log_exp]
    have h1 : 0 ≤ b * y2 := mul_nonneg hb hy2pos.le
    have h2 := mul_nonneg hk.le h1
    have h3 := neg_abs_le (k * s)
    nlinarith
  have hcont : ContinuousOn H (Set.Icc y1 y2) := by
    apply ContinuousOn.add
    · apply Real.continuousOn_log.mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le hy1pos hx.1)
    · fun_prop
  obtain ⟨y, hyI, hyH⟩ := intermediate_value_Icc (hy1le.trans hy21) hcont ⟨hH1.le, hH2.le⟩
  have hypos : 0 < y := lt_of_lt_of_le hy1pos hyI.1
  refine ⟨y, ⟨hypos, (hequiv y hypos).2 hyH⟩, ?_⟩
  rintro z ⟨hz, hzeq⟩
  have hzH := (hequiv z hz).1 hzeq
  exact hmono.injOn (Set.mem_Ioi.2 hz) (Set.mem_Ioi.2 hypos) (by rw [hzH, hyH])

lemma clu2_q_nonneg {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef) (θ : Fin n → ℝ) :
    0 ≤ quadForm S θ ∧ (θ ≠ 0 → 0 < quadForm S θ) := by
  have hinv := hS.inv
  by_cases h : θ = 0
  · subst h
    simp [quadForm]
  · have := hinv.dotProduct_mulVec_pos h
    have e : star θ = θ := by ext i; simp
    rw [e] at this
    exact ⟨this.le, fun _ => this⟩

lemma clu2_isY_iff {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (α γr γg lam : ℝ) (θ : Fin n → ℝ) (y : ℝ) :
    IsYLambda S α γr γg lam θ y ↔
      0 < y ∧ y = Real.exp (-(α * γg / lam) * (∑ i, θ i + (quadForm S θ / γr) * y)) := by
  unfold IsYLambda
  have : y / γr * quadForm S θ = quadForm S θ / γr * y := by ring
  rw [this]

lemma clu2_dot_green {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (α γr : ℝ) (θ : Fin n → ℝ) (y : ℝ) :
    θ ⬝ᵥ greenPortfolio S α γr θ y = α * (∑ i, θ i + y / γr * quadForm S θ) := by
  unfold greenPortfolio quadForm
  simp only [dotProduct]
  generalize S⁻¹ *ᵥ θ = w
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem solution {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (α γr γg : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγr : 0 < γr) (hγg : 0 < γg)
    (θ : Fin n → ℝ) :
    ∀ lam : ℝ, 0 < lam → ∃! y : ℝ, IsYLambda S α γr γg lam θ y := by
  intro lam hlam
  obtain ⟨hq, -⟩ := clu2_q_nonneg S hS θ
  have hk : 0 < α * γg / lam := by positivity
  have hb : 0 ≤ quadForm S θ / γr := div_nonneg hq hγr.le
  obtain ⟨y, hy, huniq⟩ := clu2_core (α * γg / lam) (∑ i, θ i) (quadForm S θ / γr) hk hb
  refine ⟨y, (clu2_isY_iff S α γr γg lam θ y).2 hy, ?_⟩
  intro z hz
  exact huniq z ((clu2_isY_iff S α γr γg lam θ z).1 hz)
