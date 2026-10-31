-- Prove2me | solution 1 for BuyXFree.Threshold.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:59:48.327867+00:00
-- url     : https://prove2.me/submissions/60238857-5a3e-4006-9074-1d56bf28a9b2

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model
open BuyXFree.Threshold

theorem solution(P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hJ : IsValueFn P p X J) :
    P.v + P.k + P.δ * J 0 ≥ P.δ * J X := by
  obtain ⟨hl0, hl1, hq0, hq1, hd0, hd1, hvb0, hvb, hk⟩ := hP
  obtain ⟨hJx, hJX⟩ := hJ
  have h0 := hJx 0 (by omega)
  by_contra hc
  push_neg at hc
  rw [max_eq_right hc.le, max_eq_right (by linarith)] at hJX
  have m1 := le_max_right (P.v - p + P.δ * J (0 + 1)) (P.δ * J 0)
  have m2 := le_max_right (P.v - p + P.δ * J (0 + 1)) (P.vbar + P.δ * J 0)
  have e1 : 0 ≤ P.lam * P.q := mul_nonneg hl0 hq0
  have e2 : 0 ≤ P.lam * (1 - P.q) := mul_nonneg hl0 (by linarith)
  have i1 : P.lam * (1 - P.q) * P.vbar ≤ (1 - P.δ) * J 0 := by
    nlinarith [mul_le_mul_of_nonneg_left m1 e1, mul_le_mul_of_nonneg_left m2 e2]
  have i2 : (1 - P.δ) * J X = P.lam * (1 - P.q) * P.vbar := by linear_combination hJX
  have i3 := le_of_mul_le_mul_left (by linarith : (1 - P.δ) * J X ≤ (1 - P.δ) * J 0)
    (by linarith : (0:ℝ) < 1 - P.δ)
  nlinarith [mul_le_mul_of_nonneg_left i3 hd0.le]
