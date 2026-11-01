-- Prove2me | solution 1 for CohenPriceFairness.LocalWelfare.uniform_demand_claim_weak
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-01T02:16:04.724852+00:00
-- url     : https://prove2.me/submissions/5efc8a7c-1155-47ae-8d7a-d920a51eedc4

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_demand_claim
import Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_zero_gap
import Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular

namespace CohenPriceFairness.LocalWelfare.Sol_uniform_demand_claim_weak

open CohenPriceFairness.LocalWelfare

theorem wk_mono (m : Market) (b : Prices) (k : Metric) (C C' : ℝ → Prop)
    (hw : ∀ D, C D → C' D) (h : SensitivityClaim m b k C) : SensitivityClaim m b k C' := by
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨D, hD, hCD⟩ := h.2 P hP
  exact ⟨D, hD, hw D hCD⟩

end CohenPriceFairness.LocalWelfare.Sol_uniform_demand_claim_weak

open CohenPriceFairness.LocalWelfare CohenPriceFairness.LocalWelfare.Sol_uniform_demand_claim_weak

theorem solution (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hne : bb 0 ≠ bb 1)
    (hcb : m.cost < min (bb 0) (bb 1)) (hlaw : ∀ i, m.law i = uniformLaw (bb i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .demand (fun D => D ≤ 0) := by
  rcases hc.eq_or_lt with hzero | hcpos
  · obtain ⟨hiff, hreg⟩ := uniform_profit_regular m hd hc bb hbb hcb hlaw
    have hdem := (hreg b hb).2.2.2.2.2
    have hbi := (hiff b).1 hb
    refine sensitivityClaim_of_zero_gap m b .demand _ le_rfl hb ?_ ?_
    · intro b' hb'
      have hbi' := (hiff b').1 hb'
      funext i; rw [hbi' i, hbi i]
    · show demand m 0 (b 0) = demand m 1 (b 1)
      rw [hdem 0, hdem 1, ← hzero, sub_zero, sub_zero]
      have := (hbb 0).ne'; have := (hbb 1).ne'
      field_simp
  · exact wk_mono m b .demand _ _ (fun D h => h.le)
      (uniform_demand_claim m hd hcpos bb hbb hne hcb hlaw b hb)
