-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.bayes_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:27:20.001738+00:00
-- url     : https://prove2.me/submissions/c68ce1bc-4fb3-42e7-b069-f91208924284

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) (α : ℝ) :
    (sigCov P α).det ≠ 0 ∧
    bayesCoef P α =
      ![P.teps / (P.tv + P.teps + tauP P α),
        tauP P α / (P.tv + P.teps + tauP P α),
        -(P.teta * (P.te + P.tu + α * P.te) / (P.te * P.tu + P.te * P.teta + P.tu * P.teta)) *
          (tauP P α / (P.tv + P.teps + tauP P α))] := by
  obtain ⟨htv, htxi, hteps, hte, htu, hteta, hgam⟩ := hP
  have hQ : 0 < P.tu + P.te * (α + 1) ^ 2 + α ^ 2 * P.teta := by positivity
  have hN : 0 < P.te * P.tu + (P.te + P.tu) * P.teta := by positivity
  have hK : 0 < P.te * P.tu + P.te * P.teta + P.tu * P.teta := by positivity
  have htp : 0 < tauP P α := by unfold tauP; positivity
  have hden : 0 < P.tv + P.teps + tauP P α := by positivity
  have hdet : (sigCov P α).det ≠ 0 := by
    have : (sigCov P α).det =
        (α ^ 2 * P.te * P.teps + α ^ 2 * P.te * P.tv + α ^ 2 * P.teps * P.teta +
          α ^ 2 * P.teta * P.tv + 2 * α * P.te * P.teps + 2 * α * P.te * P.tv +
          P.te * P.teps + P.te * P.teta + P.te * P.tu + P.te * P.tv + P.teps * P.tu +
          P.teta * P.tu + P.tu * P.tv) / (P.te * P.teps * P.teta * P.tu * P.tv) := by
      rw [Matrix.det_fin_three]
      simp [sigCov]
      field_simp
      ring
    rw [this]
    apply ne_of_gt
    apply div_pos _ (by positivity)
    nlinarith [sq_nonneg (α + 1), mul_pos hte hteps, mul_pos hte htv, mul_pos hteps hteta,
      mul_pos hteta htv, mul_pos hte hteta, mul_pos hte htu, mul_pos hteps htu,
      mul_pos hteta htu, mul_pos htu htv, sq_nonneg α,
      mul_nonneg (mul_pos hte hteps).le (sq_nonneg (α + 1)),
      mul_nonneg (mul_pos hte htv).le (sq_nonneg (α + 1)),
      mul_nonneg (mul_pos hteps hteta).le (sq_nonneg α),
      mul_nonneg (mul_pos hteta htv).le (sq_nonneg α)]
  refine ⟨hdet, ?_⟩
  set β : Fin 3 → ℝ := ![P.teps / (P.tv + P.teps + tauP P α),
        tauP P α / (P.tv + P.teps + tauP P α),
        -(P.teta * (P.te + P.tu + α * P.te) / (P.te * P.tu + P.te * P.teta + P.tu * P.teta)) *
          (tauP P α / (P.tv + P.teps + tauP P α))] with hβ
  have hmul : (sigCov P α).mulVec β = sigCovV P := by
    ext i
    fin_cases i <;>
      simp [hβ, sigCov, sigCovV, Matrix.mulVec, dotProduct, Fin.sum_univ_three, tauP] <;>
      field_simp <;>
      ring
  have hu : IsUnit (sigCov P α).det := isUnit_iff_ne_zero.mpr hdet
  unfold bayesCoef
  rw [← hmul, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
