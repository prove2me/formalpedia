-- Prove2me | solution 1 for FlexGroupBuy.REE.price_switch
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:09:15.180247+00:00
-- url     : https://prove2.me/submissions/96d92c52-bbb4-49a4-9028-45d5c96d42f9

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

open FlexGroupBuy.REE

theorem solution (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
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
