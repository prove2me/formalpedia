-- Prove2me | solution 1 for DrugMarket.retail_equilibrium_demand_profit
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T15:28:37.572293+00:00
-- url     : https://prove2.me/submissions/f1d67f0d-e0fc-4991-b220-1e604a358bc9

import Mathlib
import Definitions.Def_drug_market_model
import Definitions.Def_drug_market_equilibrium
namespace DrugMarket
theorem retail_equilibrium_demand_profit (t w_a w_b : ℝ) (ht : 0 < t) :
  demandA t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = (1:ℝ)/2 + (w_b - w_a)/(6*t) ∧ demandB t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = (1:ℝ)/2 + (w_a - w_b)/(6*t) ∧ (retailPriceA t w_a w_b - w_a) * demandA t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = grossProfitA t w_a w_b ∧ (retailPriceB t w_a w_b - w_b) * demandB t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = grossProfitB t w_a w_b := by
  have ht' : t ≠ 0 := ht.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [demandA, demandB, retailPriceA, retailPriceB, grossProfitA, grossProfitB] <;>
    field_simp <;> ring

end DrugMarket

open DrugMarket in
theorem solution (t w_a w_b : ℝ) (ht : 0 < t) :
  demandA t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = (1:ℝ)/2 + (w_b - w_a)/(6*t) ∧ demandB t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = (1:ℝ)/2 + (w_a - w_b)/(6*t) ∧ (retailPriceA t w_a w_b - w_a) * demandA t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = grossProfitA t w_a w_b ∧ (retailPriceB t w_a w_b - w_b) * demandB t (retailPriceA t w_a w_b) (retailPriceB t w_a w_b) = grossProfitB t w_a w_b := by
  have ht' : t ≠ 0 := ht.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [demandA, demandB, retailPriceA, retailPriceB, grossProfitA, grossProfitB] <;>
    field_simp <;> ring
