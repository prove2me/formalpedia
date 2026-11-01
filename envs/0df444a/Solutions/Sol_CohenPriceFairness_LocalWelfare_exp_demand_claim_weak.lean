-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.exp_demand_claim_weak
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:16:06.306239+00:00
-- url     : https://prove2.me/submissions/868e839e-2a99-4e16-aa26-36c2af9725af

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_demand_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_zero_gap
import Theorems.Thm_CohenPriceFairness_LocalWelfare_exp_profit_regular

open ProbabilityTheory

namespace CohenPriceFairness.LocalWelfare.Sol_exp_demand_claim_weak

theorem wk_mono (m : Market) (b : Prices) (k : Metric) (C C' : ℝ → Prop)
    (hw : ∀ D, C D → C' D) (h : SensitivityClaim m b k C) : SensitivityClaim m b k C' := by
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨D, hD, hCD⟩ := h.2 P hP
  exact ⟨D, hD, hw D hCD⟩

end CohenPriceFairness.LocalWelfare.Sol_exp_demand_claim_weak

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_exp_demand_claim_weak
open ProbabilityTheory

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (rate : Fin 2 → ℝ) (hrate : ∀ i, 0 < rate i) (hne : rate 0 ≠ rate 1)
    (hlaw : ∀ i, m.law i = expMeasure (rate i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .demand (fun D => D ≤ 0) := by
  rcases hc.eq_or_lt with hzero | hcpos
  · obtain ⟨hBO, hreg⟩ := exp_profit_regular m hd hc rate hrate hlaw
    have hdem := (hreg b hb).2.2.2.2.2
    have huniq : ∀ b' : Prices, BaselineOptimal m b' → b' = b := fun b' hb' => by
      funext i; rw [(hBO b').1 hb' i, (hBO b).1 hb i]
    refine sensitivityClaim_of_zero_gap m b .demand _ le_rfl hb huniq ?_
    show demand m 0 (b 0) = demand m 1 (b 1)
    rw [hdem 0, hdem 1, ← hzero, mul_zero, mul_zero]
  · exact wk_mono m b .demand (fun D => D < 0) _ (fun D h => h.le)
      (exp_demand_claim m hd hcpos rate hrate hne hlaw b hb)
