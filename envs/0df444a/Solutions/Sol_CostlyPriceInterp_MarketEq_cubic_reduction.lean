-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.cubic_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:27:20.828646+00:00
-- url     : https://prove2.me/submissions/0699e0ba-2d1d-4710-8e9f-4515264e373a

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) (α : ℝ) :
    (α * avOf P α = auOf P α ↔ cubicF P α = 0) ∧ 0 < avOf P α := by
  obtain ⟨htv, htxi, hteps, hte, htu, hteta, hgam⟩ := hP
  have hD : 0 < α ^ 2 * P.te * P.teps + α ^ 2 * P.te * P.tv + α ^ 2 * P.teps * P.teta +
          α ^ 2 * P.teta * P.tv + 2 * α * P.te * P.teps + 2 * α * P.te * P.tv +
          P.te * P.teps + P.te * P.teta + P.te * P.tu + P.te * P.tv + P.teps * P.tu +
          P.teta * P.tu + P.tu * P.tv := by
    nlinarith [sq_nonneg (α + 1), mul_pos hte hteps, mul_pos hte htv, mul_pos hteps hteta,
      mul_pos hteta htv, mul_pos hte hteta, mul_pos hte htu, mul_pos hteps htu,
      mul_pos hteta htu, mul_pos htu htv, sq_nonneg α,
      mul_nonneg (mul_pos hte hteps).le (sq_nonneg (α + 1)),
      mul_nonneg (mul_pos hte htv).le (sq_nonneg (α + 1)),
      mul_nonneg (mul_pos hteps hteta).le (sq_nonneg α),
      mul_nonneg (mul_pos hteta htv).le (sq_nonneg α)]
  have hQ : 0 < P.tu + P.te * (α + 1) ^ 2 + α ^ 2 * P.teta := by positivity
  have hK : 0 < P.te * P.tu + P.te * P.teta + P.tu * P.teta := by positivity
  have key : α * avOf P α - auOf P α = cubicF P α /
        (α ^ 2 * P.te * P.teps + α ^ 2 * P.te * P.tv + α ^ 2 * P.teps * P.teta +
          α ^ 2 * P.teta * P.tv + 2 * α * P.te * P.teps + 2 * α * P.te * P.tv +
          P.te * P.teps + P.te * P.teta + P.te * P.tu + P.te * P.tv + P.teps * P.tu +
          P.teta * P.tu + P.tu * P.tv) := by
    rw [eq_div_iff hD.ne']
    have htp : 0 < tauP P α := by unfold tauP; positivity
    have hden : 0 < P.tv + P.teps + tauP P α := by positivity
    have htpd : tauP P α * (P.tu + P.te * (α + 1) ^ 2 + α ^ 2 * P.teta) =
        P.te * P.tu + (P.te + P.tu) * P.teta := by
      unfold tauP; field_simp
    have h1 : avOf P α * (P.tv + P.teps + tauP P α) = P.teps + tauP P α := by
      unfold avOf; field_simp
    have h2 : auOf P α * (P.tv + P.teps + tauP P α) * (P.te * P.tu + P.te * P.teta + P.tu * P.teta)
        = tauP P α * (P.tu * (P.te + α * P.te + α * P.teta)) := by
      unfold auOf; field_simp
    unfold cubicF
    apply mul_right_cancel₀ hK.ne'
    linear_combination (α * (P.te * P.tu + P.te * P.teta + P.tu * P.teta) *
        (P.tu + P.te * (α + 1) ^ 2 + α ^ 2 * P.teta)) * h1
      - (P.tu + P.te * (α + 1) ^ 2 + α ^ 2 * P.teta) * h2
      + (α * (P.te * P.tu + P.te * P.teta + P.tu * P.teta) * (1 - avOf P α)
        - P.tu * (P.te + α * P.te + α * P.teta) + auOf P α * (P.te * P.tu + P.te * P.teta + P.tu * P.teta)) * htpd
  constructor
  · constructor
    · intro h
      have h0 := key
      rw [h, sub_self] at h0
      exact (div_eq_zero_iff.mp h0.symm).resolve_right hD.ne'
    · intro h
      have : α * avOf P α - auOf P α = 0 := by rw [key, h, zero_div]
      linarith
  · unfold avOf tauP; positivity
