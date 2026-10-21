-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.uniqueness_discriminant
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:27:23.505784+00:00
-- url     : https://prove2.me/submissions/2b05c1b5-7873-41d8-a9b8-6da9857f7b81

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) :
    (∀ x : ℝ, (cubic18 P).toPoly.eval x = cubicF P x) ∧
    (cubic18 P).discr = -P.teps *
      (4 * P.te ^ 3 * P.teta ^ 4 + 4 * P.te ^ 4 * P.teta ^ 3 + 4 * P.te * P.tu ^ 3 * P.teps ^ 3
        + 4 * P.te ^ 3 * P.tu * P.teps ^ 3 + 4 * P.te ^ 4 * P.tu * P.teps ^ 2
        + 27 * P.te ^ 4 * P.tu ^ 2 * P.teps
        + 12 * P.te ^ 3 * P.teps * P.teta ^ 3 + 4 * P.te ^ 3 * P.teps ^ 3 * P.teta
        + 8 * P.te ^ 4 * P.teps * P.teta ^ 2 + 4 * P.te ^ 4 * P.teps ^ 2 * P.teta
        + 4 * P.tu ^ 3 * P.teps ^ 3 * P.teta + 8 * P.te ^ 2 * P.tu ^ 2 * P.teps ^ 3
        + 36 * P.te ^ 3 * P.tu ^ 2 * P.teps ^ 2 + 12 * P.te ^ 3 * P.teps ^ 2 * P.teta ^ 2
        + 12 * P.te * P.tu ^ 2 * P.teps ^ 2 * P.teta ^ 2
        + 24 * P.te ^ 2 * P.tu * P.teps ^ 2 * P.teta ^ 2
        + 27 * P.te ^ 2 * P.tu ^ 2 * P.teps * P.teta ^ 2
        + 48 * P.te ^ 2 * P.tu ^ 2 * P.teps ^ 2 * P.teta
        + 36 * P.te ^ 4 * P.tu * P.teps * P.teta
        + 12 * P.te * P.tu ^ 2 * P.teps ^ 3 * P.teta
        + 12 * P.te ^ 2 * P.tu * P.teps * P.teta ^ 3
        + 12 * P.te ^ 2 * P.tu * P.teps ^ 3 * P.teta
        + 48 * P.te ^ 3 * P.tu * P.teps * P.teta ^ 2
        + 52 * P.te ^ 3 * P.tu * P.teps ^ 2 * P.teta
        + 54 * P.te ^ 3 * P.tu ^ 2 * P.teps * P.teta) ∧
    (cubic18 P).discr < 0 ∧
    ∀ x y : ℝ, cubicF P x = 0 → cubicF P y = 0 → x = y := by
  obtain ⟨htv, htxi, hteps, hte, htu, hteta, hgam⟩ := hP
  have hev : ∀ x : ℝ, (cubic18 P).toPoly.eval x = cubicF P x := by
    intro x
    simp [Cubic.toPoly, cubic18, cubicF]
    ring
  have hdisc : (cubic18 P).discr = -P.teps *
      (4 * P.te ^ 3 * P.teta ^ 4 + 4 * P.te ^ 4 * P.teta ^ 3 + 4 * P.te * P.tu ^ 3 * P.teps ^ 3
        + 4 * P.te ^ 3 * P.tu * P.teps ^ 3 + 4 * P.te ^ 4 * P.tu * P.teps ^ 2
        + 27 * P.te ^ 4 * P.tu ^ 2 * P.teps
        + 12 * P.te ^ 3 * P.teps * P.teta ^ 3 + 4 * P.te ^ 3 * P.teps ^ 3 * P.teta
        + 8 * P.te ^ 4 * P.teps * P.teta ^ 2 + 4 * P.te ^ 4 * P.teps ^ 2 * P.teta
        + 4 * P.tu ^ 3 * P.teps ^ 3 * P.teta + 8 * P.te ^ 2 * P.tu ^ 2 * P.teps ^ 3
        + 36 * P.te ^ 3 * P.tu ^ 2 * P.teps ^ 2 + 12 * P.te ^ 3 * P.teps ^ 2 * P.teta ^ 2
        + 12 * P.te * P.tu ^ 2 * P.teps ^ 2 * P.teta ^ 2
        + 24 * P.te ^ 2 * P.tu * P.teps ^ 2 * P.teta ^ 2
        + 27 * P.te ^ 2 * P.tu ^ 2 * P.teps * P.teta ^ 2
        + 48 * P.te ^ 2 * P.tu ^ 2 * P.teps ^ 2 * P.teta
        + 36 * P.te ^ 4 * P.tu * P.teps * P.teta
        + 12 * P.te * P.tu ^ 2 * P.teps ^ 3 * P.teta
        + 12 * P.te ^ 2 * P.tu * P.teps * P.teta ^ 3
        + 12 * P.te ^ 2 * P.tu * P.teps ^ 3 * P.teta
        + 48 * P.te ^ 3 * P.tu * P.teps * P.teta ^ 2
        + 52 * P.te ^ 3 * P.tu * P.teps ^ 2 * P.teta
        + 54 * P.te ^ 3 * P.tu ^ 2 * P.teps * P.teta) := by
    simp [Cubic.discr, cubic18]
    ring
  refine ⟨hev, hdisc, ?_, ?_⟩
  · rw [hdisc, neg_mul]
    apply neg_neg_of_pos
    positivity
  · -- f < 0 on (-∞, 0], strictly increasing on (0, ∞)
    have hnonpos : ∀ x : ℝ, x ≤ 0 → cubicF P x < 0 := by
      intro x hx
      unfold cubicF
      have e : (P.te * P.teps + P.teps * P.teta) * x ^ 3 + 2 * P.te * P.teps * x ^ 2
          + (P.te * P.teps + P.te * P.teta + P.tu * P.teps) * x - P.te * P.tu =
          P.te * P.teps * (x * (x + 1) ^ 2) + P.teps * P.teta * (x * x ^ 2)
          + (P.te * P.teta + P.tu * P.teps) * x - P.te * P.tu := by ring
      rw [e]
      have a1 : x * (x + 1) ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx (sq_nonneg _)
      have a2 : x * x ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx (sq_nonneg _)
      have b1 := mul_nonpos_of_nonneg_of_nonpos (mul_pos hte hteps).le a1
      have b2 := mul_nonpos_of_nonneg_of_nonpos (mul_pos hteps hteta).le a2
      have b3 := mul_nonpos_of_nonneg_of_nonpos
        (by positivity : (0:ℝ) ≤ P.te * P.teta + P.tu * P.teps) hx
      nlinarith [mul_pos hte htu]
    have hmono : ∀ x y : ℝ, 0 < x → x < y → cubicF P x < cubicF P y := by
      intro x y hx hxy
      unfold cubicF
      have hy : 0 < y := lt_trans hx hxy
      have e1 : x ^ 3 < y ^ 3 := by gcongr
      have e2 : x ^ 2 < y ^ 2 := by gcongr
      have c1 : 0 < P.te * P.teps + P.teps * P.teta := by positivity
      have c2 : 0 < 2 * P.te * P.teps := by positivity
      have c3 : 0 < P.te * P.teps + P.te * P.teta + P.tu * P.teps := by positivity
      nlinarith [mul_lt_mul_of_pos_left e1 c1, mul_lt_mul_of_pos_left e2 c2,
        mul_lt_mul_of_pos_left hxy c3]
    have hpos : ∀ x : ℝ, cubicF P x = 0 → 0 < x := by
      intro x hx
      by_contra h
      have := hnonpos x (not_lt.mp h)
      linarith
    intro x y hx hy
    have px := hpos x hx
    have py := hpos y hy
    rcases lt_trichotomy x y with h | h | h
    · have := hmono x y px h; linarith
    · exact h
    · have := hmono y x py h; linarith
