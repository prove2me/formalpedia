-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.existence_ivt
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:27:21.808461+00:00
-- url     : https://prove2.me/submissions/4ebf7b74-12ba-4f3f-883f-59262bf30b94

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) :
    cubicF P 0 = -(P.te * P.tu) ∧ cubicF P 0 < 0 ∧ 0 < cubicF P (alphaBar P) ∧
      ∃ α ∈ Set.Ioo 0 (alphaBar P), cubicF P α = 0 := by
  obtain ⟨htv, htxi, hteps, hte, htu, hteta, hgam⟩ := hP
  have h0 : cubicF P 0 = -(P.te * P.tu) := by unfold cubicF; ring
  have hM : 0 < P.te * P.teps + P.te * P.teta + P.tu * P.teps := by positivity
  have hab : 0 < alphaBar P := by unfold alphaBar; positivity
  have h1 : 0 < cubicF P (alphaBar P) := by
    have : cubicF P (alphaBar P) = (P.te * P.teps + P.teps * P.teta) * alphaBar P ^ 3 +
        2 * P.te * P.teps * alphaBar P ^ 2 := by
      unfold cubicF
      have : (P.te * P.teps + P.te * P.teta + P.tu * P.teps) * alphaBar P = P.te * P.tu := by
        unfold alphaBar; field_simp
      linarith
    rw [this]; positivity
  have hneg : cubicF P 0 < 0 := by rw [h0]; nlinarith [mul_pos hte htu]
  refine ⟨h0, hneg, h1, ?_⟩
  have hc : ContinuousOn (cubicF P) (Set.Icc 0 (alphaBar P)) := by
    unfold cubicF; fun_prop
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo hab.le hc ⟨hneg, h1⟩
  exact ⟨x, hx, hfx⟩
