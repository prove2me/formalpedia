-- Prove2me | solution 1 for DermanSeqDecisions.Stationary.total_cost_abel_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T05:26:48.414559+00:00
-- url     : https://prove2.me/submissions/0bc3e107-4975-429e-ab27-f4438712264b

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Model
import Definitions.Def_SennottDP_AvgFinite_Criteria
import Definitions.Def_DermanSeqDecisions_Stationary_totalCost

set_option autoImplicit false

open scoped ENNReal NNReal Topology
open SennottDP.AvgFinite Filter

theorem abel_tendsto_ennreal_9d53 (E : ℕ → ℝ≥0∞) :
    Tendsto (fun α : ℝ => ∑' t : ℕ, ENNReal.ofReal α ^ t * E t) (𝓝[<] 1)
      (𝓝 (∑' t, E t)) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · rw [ENNReal.tsum_eq_iSup_nat] at hb
    obtain ⟨N, hN⟩ := lt_iSup_iff.1 hb
    have hcont : Tendsto (fun α : ℝ => ∑ t ∈ Finset.range N, ENNReal.ofReal α ^ t * E t)
        (𝓝[<] 1) (𝓝 (∑ t ∈ Finset.range N, E t)) := by
      apply tendsto_finsetSum
      intro t _
      have h1 : Tendsto (fun α : ℝ => ENNReal.ofReal α ^ t) (𝓝[<] 1) (𝓝 1) := by
        have h0 : Tendsto (fun α : ℝ => ENNReal.ofReal α) (𝓝[<] 1) (𝓝 1) := by
          have := (ENNReal.continuous_ofReal.tendsto 1).mono_left
            (nhdsWithin_le_nhds (s := Set.Iio (1:ℝ)))
          simpa using this
        have h2 := ((ENNReal.continuous_pow t).tendsto 1).comp h0
        rw [one_pow] at h2
        exact h2
      simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
    filter_upwards [(tendsto_order.1 hcont).1 b hN] with α hα
    exact lt_of_lt_of_le hα (ENNReal.sum_le_tsum _)
  · filter_upwards [self_mem_nhdsWithin] with α (hα : α < 1)
    refine lt_of_le_of_lt ?_ hb
    refine ENNReal.tsum_le_tsum fun t => ?_
    have : ENNReal.ofReal α ≤ 1 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hα.le
    exact mul_le_of_le_one_left bot_le (pow_le_one₀ bot_le this)

open SennottDP.AvgFinite Filter Topology DermanSeqDecisions.Stationary in
theorem solution {S : Type*} {Act : Type*} [Fintype S] [Nonempty S]
    [Fintype Act] [Nonempty Act]
    (M : MDC S Act) (hA : ∀ i, M.A i = Finset.univ) (θ : Policy M) (i : S) :
    Tendsto (fun α : ℝ => discCost θ α i) (𝓝[<] 1) (𝓝 (totalCost θ i)) := by
  exact abel_tendsto_ennreal_9d53 (fun t => expCost θ i t)
