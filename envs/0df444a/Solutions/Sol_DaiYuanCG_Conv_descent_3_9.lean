-- Prove2me | solution 1 for DaiYuanCG.Conv.descent_3_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:48:02.361254+00:00
-- url     : https://prove2.me/submissions/76fc9317-4b20-4e50-9a09-3f16225d0bec

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

set_option autoImplicit false

open DaiYuanCG.Conv

namespace DYCAux

lemma eq25 {n : ℕ} (f : E n → ℝ) (x d : ℕ → E n) (α : ℕ → ℝ)
    (hit : IsDYIteration f x d α) (k : ℕ) (hk : 1 ≤ k)
    (hy : inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) ≠ 0) :
    inner ℝ (gradient f (x (k + 1))) (d (k + 1)) =
        ‖gradient f (x (k + 1))‖ ^ 2 /
          inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) *
          inner ℝ (gradient f (x k)) (d k) ∧
      inner ℝ (gradient f (x (k + 1))) (d (k + 1)) =
        betaDY f x d k * inner ℝ (gradient f (x k)) (d k) := by
  obtain ⟨_, hstep⟩ := hit
  obtain ⟨_, _, hd⟩ := hstep k hk
  have hbeta : betaDY f x d k = ‖gradient f (x (k + 1))‖ ^ 2 /
      inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) := rfl
  suffices h : inner ℝ (gradient f (x (k + 1))) (d (k + 1)) =
      betaDY f x d k * inner ℝ (gradient f (x k)) (d k) by
    refine ⟨?_, h⟩
    rw [h, hbeta]
  have h1 : inner ℝ (gradient f (x (k + 1))) (d (k + 1)) =
      -‖gradient f (x (k + 1))‖ ^ 2 + betaDY f x d k * inner ℝ (gradient f (x (k + 1))) (d k) := by
    rw [hd, inner_add_right, inner_neg_right, real_inner_self_eq_norm_sq, inner_smul_right]
  have h2 : betaDY f x d k * inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k))
      = ‖gradient f (x (k + 1))‖ ^ 2 := by
    rw [hbeta]; exact div_mul_cancel₀ _ hy
  rw [inner_sub_right, real_inner_comm (gradient f (x (k + 1))) (d k),
    real_inner_comm (gradient f (x k)) (d k)] at h2
  rw [h1]
  linarith

lemma descent {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hrun : IsDYRun f δ σ x d α)
    (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0 ∧
      (σ - 1) * inner ℝ (d k) (gradient f (x k)) ≤
        inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) ∧
      0 < inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) := by
  have hmain : ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [hrun.1.1, inner_neg_right, real_inner_self_eq_norm_sq]
      exact neg_neg_of_pos (pow_pos (norm_pos_iff.2 (hnt 1 le_rfl)) 2)
    | succ k hk ih =>
      have hcurv := (hrun.2 k hk).2
      have hxk : x (k + 1) = x k + α k • d k := (hrun.1.2 k hk).2.1
      rw [← hxk] at hcurv
      have hy : (σ - 1) * inner ℝ (d k) (gradient f (x k)) ≤
          inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) := by
        rw [inner_sub_right, real_inner_comm (gradient f (x (k + 1))) (d k),
          real_inner_comm (gradient f (x k)) (d k)]
        nlinarith [hcurv]
      have hypos : 0 < inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) := by
        rw [real_inner_comm] at ih
        nlinarith [hy, ih, hσ1]
      have h25 := (eq25 f x d α hrun.1 k hk hypos.ne').2
      have hβ : 0 < betaDY f x d k :=
        div_pos (pow_pos (norm_pos_iff.2 (hnt (k + 1) (by omega))) 2) hypos
      rw [h25]
      exact mul_neg_of_pos_of_neg hβ ih
  intro k hk
  have h1 := hmain k hk
  have hcurv := (hrun.2 k hk).2
  have hxk : x (k + 1) = x k + α k • d k := (hrun.1.2 k hk).2.1
  rw [← hxk] at hcurv
  have hy : (σ - 1) * inner ℝ (d k) (gradient f (x k)) ≤
      inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) := by
    rw [inner_sub_right, real_inner_comm (gradient f (x (k + 1))) (d k),
      real_inner_comm (gradient f (x k)) (d k)]
    nlinarith [hcurv]
  refine ⟨h1, hy, ?_⟩
  rw [real_inner_comm] at h1
  nlinarith [hy, h1, hσ1]

lemma eq314 {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hrun : IsDYRun f δ σ x d α)
    (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    ∀ k, 1 ≤ k → ‖d k‖ ^ 2 / inner ℝ (gradient f (x k)) (d k) ^ 2 ≤
      ∑ i ∈ Finset.Icc 1 k, 1 / ‖gradient f (x i)‖ ^ 2 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    have hg : 0 < ‖gradient f (x 1)‖ := norm_pos_iff.2 (hnt 1 le_rfl)
    rw [hrun.1.1, norm_neg, inner_neg_right, real_inner_self_eq_norm_sq]
    simp only [Finset.Icc_self, Finset.sum_singleton]
    apply le_of_eq
    have hg2 : ‖gradient f (x 1)‖ ^ 2 ≠ 0 := by positivity
    field_simp
  | succ k hk ih =>
    obtain ⟨hdesc, hy1, hypos⟩ := descent f δ σ hσ1 x d α hrun hnt k hk
    have hdesc1 := (descent f δ σ hσ1 x d α hrun hnt (k + 1) (by omega)).1
    have h25 := (eq25 f x d α hrun.1 k hk hypos.ne').2
    have hβ : 0 < betaDY f x d k :=
      div_pos (pow_pos (norm_pos_iff.2 (hnt (k + 1) (by omega))) 2) hypos
    have hd := (hrun.1.2 k hk).2.2
    set a := inner ℝ (gradient f (x k)) (d k) with ha
    set b := inner ℝ (gradient f (x (k + 1))) (d (k + 1)) with hb
    set β := betaDY f x d k with hβdef
    set G := ‖gradient f (x (k + 1))‖ ^ 2 with hG
    set N := ‖d k‖ ^ 2 with hN
    set M := ‖d (k + 1)‖ ^ 2 with hM
    have hGpos : 0 < G := pow_pos (norm_pos_iff.2 (hnt (k + 1) (by omega))) 2
    have hMeq : M = β ^ 2 * N - 2 * b - G := by
      have h1 : β • d k = d (k + 1) + gradient f (x (k + 1)) := by
        rw [hd]; abel
      have h2 : ‖β • d k‖ ^ 2 = ‖d (k + 1) + gradient f (x (k + 1))‖ ^ 2 := by rw [h1]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_add_sq_real, real_inner_comm] at h2
      rw [hM, hN, hG, hb]
      linarith
    have hbeq : b = β * a := h25
    have ha0 : a ≠ 0 := hdesc.ne
    have hb0 : b ≠ 0 := hdesc1.ne
    have hb2 : 0 < b ^ 2 := by positivity
    rw [Finset.sum_Icc_succ_top (by omega)]
    have key : (N / a ^ 2 + 1 / G) * b ^ 2 - M = (b + G) ^ 2 / G := by
      rw [hMeq, hbeq]
      field_simp
      ring
    have h3 : M / b ^ 2 ≤ N / a ^ 2 + 1 / G := by
      rw [div_le_iff₀ hb2]
      have := div_nonneg (sq_nonneg (b + G)) hGpos.le
      linarith
    have ih' : N / a ^ 2 ≤ ∑ i ∈ Finset.Icc 1 k, 1 / ‖gradient f (x i)‖ ^ 2 := ih
    have hGe : 1 / G = 1 / ‖gradient f (x (k + 1))‖ ^ 2 := rfl
    linarith

end DYCAux

open DYCAux

theorem solution {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hrun : IsDYRun f δ σ x d α)
    (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0 ∧
      (σ - 1) * inner ℝ (d k) (gradient f (x k)) ≤
        inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) ∧
      0 < inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) :=
  descent f δ σ hσ1 x d α hrun hnt
