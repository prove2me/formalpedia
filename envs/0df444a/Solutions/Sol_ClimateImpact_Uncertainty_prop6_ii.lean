-- Prove2me | solution 1 for ClimateImpact.Uncertainty.prop6_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:34:06.727671+00:00
-- url     : https://prove2.me/submissions/683fe209-97c1-4819-ae7e-5f5adaac86f0

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
    (θ : Fin n → ℝ)
    (Y : ℝ → ℝ) (hY : ∀ lam : ℝ, 0 < lam → IsYLambda S α γr γg lam θ (Y lam))
    (hpos : 0 < θ ⬝ᵥ greenPortfolio S α γr θ 1) :
    (∀ lam : ℝ, 0 < lam → 0 < Y lam) ∧
    StrictMonoOn Y (Set.Ioi 0) ∧
    Filter.Tendsto Y Filter.atTop (nhds 1) ∧
    StrictMonoOn (fun lam => θ ⬝ᵥ greenPortfolio S α γr θ (Y lam)) (Set.Ioi 0) ∧
    (∀ i, θ i < 0 → StrictMonoOn (fun lam => expectedReturn S α γr γg θ (Y lam) i) (Set.Ioi 0)) ∧
    (∀ i, 0 < θ i → StrictAntiOn (fun lam => expectedReturn S α γr γg θ (Y lam) i) (Set.Ioi 0)) := by
  obtain ⟨hq, hqpos⟩ := clu2_q_nonneg S hS θ
  have hθne : θ ≠ 0 := by
    intro h
    rw [h] at hpos
    simp at hpos
  have hbpos : 0 < quadForm S θ / γr := div_pos (hqpos hθne) hγr
  set s : ℝ := ∑ i, θ i with hs
  set b : ℝ := quadForm S θ / γr with hbdef
  have hsb : 0 < s + b := by
    have h1 := hpos
    rw [clu2_dot_green] at h1
    have h := (mul_pos_iff_of_pos_left hα0).1 h1
    have e : 1 / γr * quadForm S θ = b := by rw [hbdef]; ring
    linarith
  have hsol : ∀ lam : ℝ, 0 < lam → 0 < Y lam ∧
      Real.log (Y lam) = -(α * γg / lam) * (s + b * Y lam) := by
    intro lam hlam
    obtain ⟨h1, h2⟩ := (clu2_isY_iff S α γr γg lam θ (Y lam)).1 (hY lam hlam)
    have := congrArg Real.log h2
    rw [Real.log_exp] at this
    exact ⟨h1, this⟩
  have hk : ∀ lam : ℝ, 0 < lam → 0 < α * γg / lam := fun lam hlam => by positivity
  have hlt1 : ∀ lam : ℝ, 0 < lam → Y lam < 1 ∧ 0 < s + b * Y lam := by
    intro lam hlam
    obtain ⟨hy0, hlog⟩ := hsol lam hlam
    have hk0 := hk lam hlam
    have hy1 : Y lam < 1 := by
      by_contra hge
      push_neg at hge
      have h1 := Real.log_nonneg hge
      have h2 : b * 1 ≤ b * Y lam := mul_le_mul_of_nonneg_left hge hbpos.le
      have h3 : 0 < (α * γg / lam) * (s + b * Y lam) := mul_pos hk0 (by linarith)
      nlinarith
    refine ⟨hy1, ?_⟩
    have h1 := Real.log_neg hy0 hy1
    by_contra hP
    push_neg at hP
    have h3 : (α * γg / lam) * (s + b * Y lam) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hk0.le hP
    nlinarith
  have hmono : StrictMonoOn Y (Set.Ioi 0) := by
    intro l1 hl1 l2 hl2 hlt
    have hl1' : 0 < l1 := hl1
    have hl2' : 0 < l2 := hl2
    by_contra hge
    push_neg at hge
    obtain ⟨hy1, hlog1⟩ := hsol l1 hl1'
    obtain ⟨hy2, hlog2⟩ := hsol l2 hl2'
    obtain ⟨-, hP1⟩ := hlt1 l1 hl1'
    obtain ⟨-, hP2⟩ := hlt1 l2 hl2'
    have hlogle := Real.log_le_log hy2 hge
    have hkk : α * γg / l2 < α * γg / l1 := div_lt_div_of_pos_left (mul_pos hα0 hγg) hl1' hlt
    have hk2 := hk l2 hl2'
    have hPP : s + b * Y l2 ≤ s + b * Y l1 := by
      have := mul_le_mul_of_nonneg_left hge hbpos.le
      linarith
    nlinarith [mul_nonneg (hk l1 hl1').le (sub_nonneg.2 hPP), mul_pos (sub_pos.2 hkk) hP2]
  refine ⟨fun lam hlam => (hsol lam hlam).1, hmono, ?_, ?_, ?_, ?_⟩
  · -- limit
    set C : ℝ := |s| + b with hC
    have h0 : Filter.Tendsto (fun lam : ℝ => α * γg / lam * C) Filter.atTop (nhds 0) := by
      have h := (tendsto_const_nhds (x := α * γg)).div_atTop Filter.tendsto_id
      have h' := h.mul_const C
      rw [zero_mul] at h'
      exact h'
    have hg : Filter.Tendsto (fun lam : ℝ => Real.exp (-(α * γg / lam * C))) Filter.atTop (nhds 1) := by
      have h0' : Filter.Tendsto (fun lam : ℝ => -(α * γg / lam * C)) Filter.atTop (nhds 0) := by
        simpa using h0.neg
      have h := (Real.continuous_exp.tendsto 0).comp h0'
      rw [Real.exp_zero] at h
      exact h
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg tendsto_const_nhds ?_ ?_
    · filter_upwards [Filter.eventually_gt_atTop 0] with lam hlam
      obtain ⟨hy0, hlog⟩ := hsol lam hlam
      obtain ⟨hy1, hP⟩ := hlt1 lam hlam
      have hk0 := hk lam hlam
      have hPle : s + b * Y lam ≤ C := by
        have h1 : b * Y lam ≤ b * 1 := mul_le_mul_of_nonneg_left hy1.le hbpos.le
        have := le_abs_self s
        rw [hC]; linarith
      have : -(α * γg / lam * C) ≤ Real.log (Y lam) := by
        rw [hlog]
        have := mul_le_mul_of_nonneg_left hPle hk0.le
        linarith
      calc Real.exp (-(α * γg / lam * C)) ≤ Real.exp (Real.log (Y lam)) := Real.exp_le_exp.2 this
        _ = Y lam := Real.exp_log hy0
    · filter_upwards [Filter.eventually_gt_atTop 0] with lam hlam
      exact (hlt1 lam hlam).1.le
  · intro l1 hl1 l2 hl2 hlt
    have := hmono hl1 hl2 hlt
    show θ ⬝ᵥ greenPortfolio S α γr θ (Y l1) < θ ⬝ᵥ greenPortfolio S α γr θ (Y l2)
    rw [clu2_dot_green, clu2_dot_green]
    have e : ∀ y : ℝ, y / γr * quadForm S θ = b * y := fun y => by rw [hbdef]; ring
    rw [e, e]
    have := mul_lt_mul_of_pos_left this hbpos
    nlinarith
  · intro i hi l1 hl1 l2 hl2 hlt
    have := hmono hl1 hl2 hlt
    show expectedReturn S α γr γg θ (Y l1) i < expectedReturn S α γr γg θ (Y l2) i
    unfold expectedReturn
    nlinarith [mul_pos (mul_pos hα0 (sub_pos.2 this)) (neg_pos.2 hi)]
  · intro i hi l1 hl1 l2 hl2 hlt
    have := hmono hl1 hl2 hlt
    show expectedReturn S α γr γg θ (Y l2) i < expectedReturn S α γr γg θ (Y l1) i
    unfold expectedReturn
    nlinarith [mul_pos (mul_pos hα0 (sub_pos.2 this)) hi]
