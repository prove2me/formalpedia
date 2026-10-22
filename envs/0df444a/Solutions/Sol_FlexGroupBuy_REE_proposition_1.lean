-- Prove2me | solution 1 for FlexGroupBuy.REE.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:26:37.739994+00:00
-- url     : https://prove2.me/submissions/f8bcd521-dbb1-4c07-b935-a2f6ab417b26

import Mathlib
import Definitions.Def_FlexGroupBuy_REE_Model

open FlexGroupBuy.REE

theorem solution (P : Params) (hP : P.Standing) (N : ℕ) (hN : 1 ≤ N)
    (x : ℝ) (hx0 : 0 ≤ x) (hxN : x < N) (p r : ℝ) :
    ¬ ((∀ n : ℕ, 1 ≤ n → n ≤ N → P.theta * P.L - p - P.c * wII P x n ≥ 0) ∧
       (∀ n : ℕ, 1 ≤ n → n ≤ N → P.theta * P.L - p - P.c * wII P x n ≥ P.L - r) ∧
       (∀ n : ℕ, x < (n : ℝ) → n ≤ N → P.H - r ≥ 0) ∧
       (∀ n : ℕ, x < (n : ℝ) → n ≤ N → P.H - r ≥ P.theta * P.H - p - P.c * wII P x n) ∧
       (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x → P.theta * P.H - p - P.c * wII P x n ≥ 0) ∧
       (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x → P.theta * P.H - p - P.c * wII P x n ≥ P.H - r)) := by
  rintro ⟨_, h2, _, h4, _, _⟩
  obtain ⟨hL, hLH, -, -, -, -, hθ⟩ := hP
  have a := h2 N hN le_rfl
  have b := h4 N hxN le_rfl
  nlinarith [mul_pos (sub_pos.2 hθ) (sub_pos.2 hLH)]

