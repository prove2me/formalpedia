-- Prove2me | solution 1 for FlexGroupBuy.REE.early_branch
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:09:13.629257+00:00
-- url     : https://prove2.me/submissions/cde61e99-05d6-4304-be49-0678d0ed9f1e

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

open FlexGroupBuy.REE

theorem t_price_switch (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    ∀ x ∈ Set.Icc (0 : ℝ) N, pbar1 P x < pbar2 P N x ↔ xbar1 P N < x := by
  obtain ⟨hL, hLH, hg0, hg1, hl, hc, ht⟩ := hP
  intro x ⟨hx0, hxN⟩
  have hK : 0 < (P.theta - 1) * (P.H - P.L) * P.gam * P.lam / P.c := by
    apply div_pos _ hc
    apply mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hg0) hl
  rcases lt_or_eq_of_le hxN with hlt | heq
  · have e1 : pbar2 P N x - pbar1 P x =
        ((P.theta - 1) * (P.H - P.L) * P.gam * P.lam - P.c * (N - 1 + P.gam - x))
          / (P.gam * P.lam) := by
      unfold pbar1 pbar2 wG
      rw [if_pos (le_refl x), if_neg (by linarith)]
      field_simp; ring
    have e2 : x - xbar1 P N =
        ((P.theta - 1) * (P.H - P.L) * P.gam * P.lam - P.c * (N - 1 + P.gam - x)) / P.c := by
      unfold xbar1; field_simp; ring
    rw [← sub_pos, e1, ← sub_pos (a := x) (b := xbar1 P N), e2,
      div_pos_iff_of_pos_right (mul_pos hg0 hl), div_pos_iff_of_pos_right hc]
  · subst heq
    have h1 : pbar1 P N < pbar2 P N N := by
      unfold pbar1 pbar2; nlinarith
    have h2 : xbar1 P N < N := by
      unfold xbar1; linarith
    exact ⟨fun _ => h2, fun _ => h1⟩

theorem t_profit_formula (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    ∀ x ∈ Set.Icc (0 : ℝ) N,
      piG P N x = (pG P N x * P.gam * P.lam * N + P.L * (1 - P.gam) * P.lam * (N - x))
        / (N - (1 - P.gam) * x) := by
  obtain ⟨hL, hLH, hg0, hg1, hl, hc, ht⟩ := hP
  intro x ⟨hx0, hxN⟩
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : 0 < (N : ℝ) - (1 - P.gam) * x := by nlinarith
  have hD2 : 0 < x / P.lam + (N - x) / (P.gam * P.lam) := by
    have : 0 ≤ x / P.lam := div_nonneg hx0 hl.le
    have : 0 ≤ ((N : ℝ) - x) / (P.gam * P.lam) := div_nonneg (by linarith) (by positivity)
    rcases lt_or_eq_of_le hxN with h | h
    · have : 0 < ((N : ℝ) - x) / (P.gam * P.lam) := div_pos (by linarith) (by positivity)
      linarith
    · subst h; have : 0 < (N : ℝ) / P.lam := div_pos (by linarith) hl
      linarith
  unfold piG rG
  generalize pG P N x = p
  rw [div_eq_div_iff hD2.ne' hD.ne']
  field_simp
  ring

theorem solution (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
    (∀ x ∈ Set.Icc (0 : ℝ) N, x ≤ xbar1 P N →
      piG P N x = (((P.theta - 1) * P.H + P.L) * P.gam * P.lam * N
          + P.L * (1 - P.gam) * P.lam * (N - x) - P.c * N * ((N : ℝ) - 1)
          + P.c * (1 - P.gam) * N * x) / (N - (1 - P.gam) * x)) ∧
    (∀ x : ℝ, (1 - P.gam) * x < N →
      HasDerivAt
        (fun y : ℝ => (((P.theta - 1) * P.H + P.L) * P.gam * P.lam * N
          + P.L * (1 - P.gam) * P.lam * (N - y) - P.c * N * ((N : ℝ) - 1)
          + P.c * (1 - P.gam) * N * y) / (N - (1 - P.gam) * y))
        ((1 - P.gam) * N * (P.c + (P.theta - 1) * P.H * P.gam * P.lam)
          / (N - (1 - P.gam) * x) ^ 2) x) ∧
    (∀ x : ℝ, (1 - P.gam) * x < N →
      0 < (1 - P.gam) * N * (P.c + (P.theta - 1) * P.H * P.gam * P.lam)
          / (N - (1 - P.gam) * x) ^ 2) := by
  have hP' := hP
  obtain ⟨hL, hLH, hg0, hg1, hl, hc, ht⟩ := hP'
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  refine ⟨?_, ?_, ?_⟩
  · intro x hmem hx1
    have hxN : x < N := by
      have : xbar1 P N < N := by
        unfold xbar1
        have : 0 < (P.theta - 1) * (P.H - P.L) * P.gam * P.lam / P.c := by
          apply div_pos _ hc
          apply mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hg0) hl
        linarith
      linarith
    have hpG : pG P N x = pbar2 P N x := by
      unfold pG
      by_cases h0 : x = 0
      · rw [if_pos h0, h0]
      · rw [if_neg h0]
        have : ¬ pbar1 P x < pbar2 P N x := by
          rw [t_price_switch P hP N hN x hmem]; linarith
        rw [min_eq_right (not_lt.mp this)]
    rw [t_profit_formula P hP N hN x hmem, hpG]
    congr 1
    unfold pbar2 wG
    rw [if_neg (by linarith)]
    field_simp; ring
  · intro x hx
    have hg : (N : ℝ) - (1 - P.gam) * x ≠ 0 := by linarith
    have hnum : HasDerivAt (fun y : ℝ => ((P.theta - 1) * P.H + P.L) * P.gam * P.lam * N
          + P.L * (1 - P.gam) * P.lam * (N - y) - P.c * N * ((N : ℝ) - 1)
          + P.c * (1 - P.gam) * N * y)
        (-(P.L * (1 - P.gam) * P.lam) + P.c * (1 - P.gam) * N) x := by
      have := ((hasDerivAt_id x).const_mul
        (-(P.L * (1 - P.gam) * P.lam) + P.c * (1 - P.gam) * N)).const_add
        (((P.theta - 1) * P.H + P.L) * P.gam * P.lam * N + P.L * (1 - P.gam) * P.lam * N
          - P.c * N * ((N : ℝ) - 1))
      exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp only [id]; ring)
    have hden : HasDerivAt (fun y : ℝ => (N : ℝ) - (1 - P.gam) * y) (-(1 - P.gam)) x := by
      have := ((hasDerivAt_id x).const_mul (-(1 - P.gam))).const_add (N : ℝ)
      exact (this.congr_deriv (by ring)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp only [id]; ring)
    refine (hnum.div hden hg).congr_deriv ?_
    rw [div_left_inj' (pow_ne_zero 2 hg)]
    ring
  · intro x hx
    have hg : 0 < ((N : ℝ) - (1 - P.gam) * x) ^ 2 := by
      have : 0 < (N : ℝ) - (1 - P.gam) * x := by linarith
      positivity
    apply div_pos _ hg
    apply mul_pos (mul_pos (by linarith) (by linarith))
    have : 0 < (P.theta - 1) * P.H * P.gam * P.lam :=
      mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) hg0) hl
    linarith
