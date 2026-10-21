-- Prove2me | solution 1 for FlexGroupBuy.REE.profit_formula
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T03:09:14.423239+00:00
-- url     : https://prove2.me/submissions/1e2dc7b1-ea9f-4782-a377-cb154346c599

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

open FlexGroupBuy.REE

theorem solution (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N) :
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
