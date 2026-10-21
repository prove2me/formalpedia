-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.a_expressions
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:28:57.786768+00:00
-- url     : https://prove2.me/submissions/39ae11a5-5cdd-4509-b441-28c11bf8b475

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model
import Theorems.Thm_CostlyPriceInterp_MarketEq_bayes_coefficients

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) (α : ℝ) :
    bayesCoef P α 0 + bayesCoef P α 1 = avOf P α ∧
      bayesCoef P α 1 * (α + 1) + bayesCoef P α 2 = auOf P α := by
  have hb := (bayes_coefficients P hP α).2
  obtain ⟨htv, htxi, hteps, hte, htu, hteta, hgam⟩ := hP
  have htp : 0 < tauP P α := by unfold tauP; positivity
  have hden : 0 < P.tv + P.teps + tauP P α := by positivity
  have hK : 0 < P.te * P.tu + P.te * P.teta + P.tu * P.teta := by positivity
  rw [hb]
  constructor
  · simp [avOf]
    field_simp
  · simp [auOf]
    field_simp
    ring
