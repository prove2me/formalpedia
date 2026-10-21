-- Prove2me | solution 1 for CostlyPriceInterp.MarketEq.coefficient_matching
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:28:58.597966+00:00
-- url     : https://prove2.me/submissions/d92154d2-b27a-46fa-b70b-64b81c066b3f

import Mathlib
import Definitions.Def_CostlyPriceInterp_MarketEq_Model
import Theorems.Thm_CostlyPriceInterp_MarketEq_conditional_variance

open CostlyPriceInterp.MarketEq

theorem solution (P : Params) (hP : P.Standing) (av au : ℝ) :
    IsLinearEq P av au ↔
      av ≠ 0 ∧
        av = bayesCoef P (au / av) 0 + bayesCoef P (au / av) 1 ∧
        au = bayesCoef P (au / av) 1 * (au / av + 1) + bayesCoef P (au / av) 2 := by
  have hcv := (conditional_variance P hP (au / av)).2
  have hg : 0 < P.gam := hP.2.2.2.2.2.2
  have hd : P.gam * condVarV P (au / av) ≠ 0 := (mul_pos hg hcv).ne'
  have hiff : ∀ v u : ℝ, aggDemand P av au v u = 0 ↔
      (bayesCoef P (au / av) 0 + bayesCoef P (au / av) 1 - av) * v +
        (bayesCoef P (au / av) 1 * (au / av + 1) + bayesCoef P (au / av) 2 - au) * u = 0 := by
    intro v u
    unfold aggDemand
    rw [div_eq_zero_iff, or_iff_left hd]
    simp [dotProduct, Fin.sum_univ_three, avgSignals]
    constructor <;> intro h <;> linear_combination h
  unfold IsLinearEq
  constructor
  · rintro ⟨hav, h⟩
    have h1 := (hiff 1 0).1 (h 1 0)
    have h2 := (hiff 0 1).1 (h 0 1)
    refine ⟨hav, ?_, ?_⟩ <;> linarith
  · rintro ⟨hav, h1, h2⟩
    refine ⟨hav, fun v u => (hiff v u).2 ?_⟩
    rw [← h1, ← h2]; ring
