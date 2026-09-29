-- Prove2me | solution 1 for Freiman.perron_frequently_at_least_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:17.564171+00:00
-- url     : https://prove2.me/submissions/ad5fbca6-e99b-4d46-97a7-eed263aba342

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_perronValue_gt_digit
import Theorems.Thm_Freiman_perron_eventually_one_limit

open Freiman

theorem solution (b : ℕ → ℕ+) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 - ε < perronValue b n := by
  classical
  by_cases h : ∀ N : ℕ, ∃ n : ℕ, N≤n ∧ 2≤(b n:ℕ)
  · intro ε hε N
    obtain ⟨n, hn, hb⟩ := h N
    refine ⟨n, hn, ?_⟩
    have hd := perronValue_gt_digit b n
    have hb' : (2:ℝ) ≤ ((b n:ℕ):ℝ) := by exact_mod_cast hb
    linarith
  · push_neg at h
    obtain ⟨N, hN⟩ := h
    have hone : ∃ N : ℕ, ∀ n : ℕ, N≤n → b n=1 := by
      refine ⟨N, ?_⟩
      intro n hn
      apply Subtype.ext
      have hpos := (b n).pos
      have hlt := hN n hn
      change (b n:ℕ)=1
      omega
    have hl := perron_eventually_one_limit b hone
    intro ε hε M
    have hs : 2-ε < Real.sqrt 5 := by
      have hs0 := Real.sqrt_nonneg (5:ℝ)
      have hs2 := Real.sq_sqrt (show (0:ℝ)≤5 by norm_num)
      nlinarith
    have he := (tendsto_order.mp hl).1 (2-ε) hs
    rw [Filter.eventually_atTop] at he
    obtain ⟨K, hK⟩ := he
    exact ⟨max M K, le_max_left _ _, hK _ (le_max_right _ _)⟩
