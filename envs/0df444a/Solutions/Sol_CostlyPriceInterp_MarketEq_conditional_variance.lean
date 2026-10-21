-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.conditional_variance
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:28:57.023868+00:00
-- url     : https://prove2.me/submissions/1fa81dd5-b132-47c1-9820-fe1b799973ee

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model
import Theorems.Thm_CostlyPriceInterp_MarketEq_bayes_coefficients

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) (α : ℝ) :
    condVarV P α = (P.tv + P.teps + tauP P α)⁻¹ + P.txi⁻¹ ∧ 0 < condVarV P α := by
  have hb := (bayes_coefficients P hP α).2
  obtain ⟨htv, htxi, hteps, hte, htu, hteta, hgam⟩ := hP
  have htp : 0 < tauP P α := by unfold tauP; positivity
  have hden : 0 < P.tv + P.teps + tauP P α := by positivity
  have h1 : condVarV P α = (P.tv + P.teps + tauP P α)⁻¹ + P.txi⁻¹ := by
    unfold condVarV
    rw [hb]
    simp [sigCovV, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  refine ⟨h1, ?_⟩
  rw [h1]; positivity
