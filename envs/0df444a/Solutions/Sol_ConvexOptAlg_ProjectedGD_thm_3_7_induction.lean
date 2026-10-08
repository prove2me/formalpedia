-- Prove2me | solution 1 for ConvexOptAlg.ProjectedGD.thm_3_7_induction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:40:25.264724+00:00
-- url     : https://prove2.me/submissions/426b2602-ef81-4775-af9d-2a05ced08835

import Mathlib

theorem bd53c2d3_step (c C x d n : ℝ) (hc : 0 ≤ c) (hn : 2 ≤ n) (hC : 3 / 2 * c ≤ C)
    (hx : 0 ≤ x) (hd : d * n ≤ C) (hrec : x ^ 2 ≤ c * (d - x)) :
    x * (n + 1) ≤ C := by
  by_contra h
  rw [not_le] at h
  set y := x * (n + 1) with hy
  have hC0 : 0 ≤ C := by linarith
  have hn0 : 0 < n := by linarith
  -- n y^2 + c n (n+1) y ≤ c (n+1)^2 C
  have key : n * y ^ 2 + c * n * (n + 1) * y ≤ c * (n + 1) ^ 2 * C := by
    have h1 : n * (n + 1) ^ 2 * x ^ 2 ≤ n * (n + 1) ^ 2 * (c * (d - x)) :=
      mul_le_mul_of_nonneg_left hrec (by positivity)
    have h2 : c * (n + 1) ^ 2 * (d * n) ≤ c * (n + 1) ^ 2 * C :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    rw [hy]; nlinarith [h1, h2]
  have hyC : C < y := h
  have hy2 : C ^ 2 < y ^ 2 := by nlinarith
  have h3 : n * C ^ 2 < n * y ^ 2 := mul_lt_mul_of_pos_left hy2 hn0
  have h4 : c * n * (n + 1) * C ≤ c * n * (n + 1) * y :=
    mul_le_mul_of_nonneg_left hyC.le (by positivity)
  have h5 : c * (n + 1) ≤ n * C := by nlinarith
  have h6 : c * (n + 1) ^ 2 * C ≤ n * C ^ 2 + c * n * (n + 1) * C := by
    have : C * (c * (n + 1)) ≤ C * (n * C) := mul_le_mul_of_nonneg_left h5 hC0
    nlinarith [this]
  linarith

theorem bd53c2d3_first (c d1 x : ℝ) (hc : 0 ≤ c) (hd1 : 0 ≤ d1) (hx : 0 ≤ x)
    (hrec : x ^ 2 ≤ c * (d1 - x)) :
    x * 2 ≤ 3 / 2 * c + d1 := by
  by_contra h
  rw [not_le] at h
  have hm : 0 ≤ (3 / 2 * c + d1) / 2 := by positivity
  have hxm : (3 / 2 * c + d1) / 2 < x := by linarith
  have : ((3 / 2 * c + d1) / 2) ^ 2 + c * ((3 / 2 * c + d1) / 2) ≤ x ^ 2 + c * x := by
    nlinarith
  nlinarith

namespace ConvexOptAlg.ProjectedGD
end ConvexOptAlg.ProjectedGD

open ConvexOptAlg.ProjectedGD in
theorem solution (β D : ℝ) (hβ : 0 < β) (δ : ℕ → ℝ)
    (hnonneg : ∀ s : ℕ, 1 ≤ s → 0 ≤ δ s)
    (hrec : ∀ s : ℕ, 1 ≤ s → δ (s + 1) ^ 2 ≤ 2 * β * D ^ 2 * (δ s - δ (s + 1)))
    (s : ℕ) (hs : 1 ≤ s) :
    δ s ≤ (3 * β * D ^ 2 + δ 1) / s := by
  have hc : 0 ≤ 2 * β * D ^ 2 := by positivity
  have hd1 : 0 ≤ δ 1 := hnonneg 1 le_rfl
  have main : ∀ n : ℕ, 1 ≤ n → δ n * (n : ℝ) ≤ 3 * β * D ^ 2 + δ 1 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => simp; nlinarith
    | succ m hm ih =>
      have hx := hnonneg (m + 1) (by omega)
      have hr := hrec m hm
      push_cast
      rcases Nat.lt_or_ge m 2 with h | h
      · have hm1 : m = 1 := by omega
        subst hm1
        have := bd53c2d3_first (2 * β * D ^ 2) (δ 1) (δ (1 + 1)) hc hd1 hx hr
        norm_num at this ⊢
        linarith
      · have hn2 : (2 : ℝ) ≤ m := by exact_mod_cast h
        exact bd53c2d3_step (2 * β * D ^ 2) _ (δ (m + 1)) (δ m) m hc hn2
          (by linarith) hx ih hr
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  rw [le_div_iff₀ hspos]
  exact main s hs
