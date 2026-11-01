-- Prove2me | solution 2 for CohenPriceFairness.LocalWelfare.theorem_2_positive_cost
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:16:07.869295+00:00
-- url     : https://prove2.me/submissions/3943441b-f698-4d6c-baa4-9d52062b8831

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_profit_regular
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_price_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_nonbuyer_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_demand_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_surplus_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_price_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_nonbuyer_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_demand_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_surplus_claim

open MeasureTheory ProbabilityTheory CohenPriceFairness.LocalWelfare

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 < m.cost)
    (hf : (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧ m.cost < min (b 0) (b 1) ∧
            ∀ i, m.law i = uniformLaw (b i)) ∨
          (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
            ∀ i, m.law i = expMeasure (rate i))) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 < D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 < D) ∧
      SensitivityClaim m b .demand (fun D => D < 0) ∧
      SensitivityClaim m b .surplus (fun D => D < 0) := by
  rcases hf with ⟨bb, hbb, hne, hcb, hlaw⟩ | ⟨rate, hrate, hne, hlaw⟩
  · have hreg := uniform_profit_regular m hd hc.le bb hbb hcb hlaw
    refine ⟨⟨fun i => (bb i + m.cost) / 2, (hreg.1 _).2 fun i => rfl⟩, fun b hb => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact uniform_price_claim m hd hc.le bb hbb hne hcb hlaw b hb
    · exact uniform_nonbuyer_claim m hd hc.le bb hbb hne hcb hlaw b hb
    · exact uniform_demand_claim m hd hc bb hbb hne hcb hlaw b hb
    · exact uniform_surplus_claim m hd hc.le bb hbb hne hcb hlaw b hb
  · have hreg := exp_profit_regular m hd hc.le rate hrate hlaw
    refine ⟨⟨fun i => m.cost + 1 / rate i, (hreg.1 _).2 fun i => rfl⟩, fun b hb => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact exp_price_claim m hd hc.le rate hrate hne hlaw b hb
    · exact exp_nonbuyer_claim m hd hc.le rate hrate hne hlaw b hb
    · exact exp_demand_claim m hd hc rate hrate hne hlaw b hb
    · exact exp_surplus_claim m hd hc.le rate hrate hne hlaw b hb

