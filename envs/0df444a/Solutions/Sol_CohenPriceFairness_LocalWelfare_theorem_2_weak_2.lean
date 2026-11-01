-- Prove2me | solution 2 for CohenPriceFairness.LocalWelfare.theorem_2_weak
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:16:09.416208+00:00
-- url     : https://prove2.me/submissions/0adac92e-fa8e-44ea-b898-8eb13304bede

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_profit_regular
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_price_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_nonbuyer_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_demand_claim_weak
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_surplus_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_price_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_nonbuyer_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_demand_claim_weak
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_surplus_claim

namespace CohenPriceFairness.LocalWelfare.Sketch_theorem_2_weak

/-- A sensitivity claim with a stronger sign condition implies the one with a weaker condition. -/
theorem claim_mono {m : Market} {b : Prices} {k : Metric} {C C' : ℝ → Prop}
    (h : ∀ D, C D → C' D) (hc : SensitivityClaim m b k C) : SensitivityClaim m b k C' :=
  ⟨hc.1, fun P hP => by
    obtain ⟨D, hD, hCD⟩ := hc.2 P hP
    exact ⟨D, hD, h D hCD⟩⟩

end CohenPriceFairness.LocalWelfare.Sketch_theorem_2_weak

open MeasureTheory ProbabilityTheory CohenPriceFairness.LocalWelfare
open CohenPriceFairness.LocalWelfare.Sketch_theorem_2_weak

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 ≤ m.cost)
    (hf : (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧ m.cost < min (b 0) (b 1) ∧
            ∀ i, m.law i = uniformLaw (b i)) ∨
          (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
            ∀ i, m.law i = expMeasure (rate i))) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 ≤ D) ∧
      SensitivityClaim m b .demand (fun D => D ≤ 0) ∧
      SensitivityClaim m b .surplus (fun D => D ≤ 0) := by
  rcases hf with ⟨bb, hbb, hne, hcb, hlaw⟩ | ⟨rate, hrate, hne, hlaw⟩
  · have hreg := uniform_profit_regular m hd hc bb hbb hcb hlaw
    refine ⟨⟨fun i => (bb i + m.cost) / 2, (hreg.1 _).2 fun i => rfl⟩, fun b hb => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact claim_mono (fun _ h => h.le) (uniform_price_claim m hd hc bb hbb hne hcb hlaw b hb)
    · exact claim_mono (fun _ h => h.le) (uniform_nonbuyer_claim m hd hc bb hbb hne hcb hlaw b hb)
    · exact uniform_demand_claim_weak m hd hc bb hbb hne hcb hlaw b hb
    · exact claim_mono (fun _ h => h.le) (uniform_surplus_claim m hd hc bb hbb hne hcb hlaw b hb)
  · have hreg := exp_profit_regular m hd hc rate hrate hlaw
    refine ⟨⟨fun i => m.cost + 1 / rate i, (hreg.1 _).2 fun i => rfl⟩, fun b hb => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact claim_mono (fun _ h => h.le) (exp_price_claim m hd hc rate hrate hne hlaw b hb)
    · exact claim_mono (fun _ h => h.le) (exp_nonbuyer_claim m hd hc rate hrate hne hlaw b hb)
    · exact exp_demand_claim_weak m hd hc rate hrate hne hlaw b hb
    · exact claim_mono (fun _ h => h.le) (exp_surplus_claim m hd hc rate hrate hne hlaw b hb)

