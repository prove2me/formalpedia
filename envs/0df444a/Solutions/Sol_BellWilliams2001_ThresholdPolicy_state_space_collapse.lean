-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.state_space_collapse
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T06:08:59.764359+00:00
-- url     : https://prove2.me/submissions/852e61ef-addc-4e19-afd5-9113f3747ad5

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_residual_collapse
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_allocation_limit
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_state_coupling_from_limits

open BellWilliams2001.ThresholdPolicy
open MeasureTheory
open scoped NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ),
        IsBrownianPair P' B →
        CouplingConverges M.P P'
          (fun n ω t => ![M.Qhat n (Tstar n) ω t 0, M.Qhat n (Tstar n) ω t 1,
            M.Ihat n (Tstar n) ω t 0, M.Ihat n (Tstar n) ω t 1])
          (fun ω t => ![0, M.Qstar B ω t 1, 0, M.Istar B ω t 1]) := by
  obtain ⟨c₁,hc₁,hResidual⟩ := residual_collapse M
  obtain ⟨c₂,_,hFluid⟩ := fluid_allocation_limit M
  refine ⟨max c₁ c₂,hc₁.trans_le (le_max_left _ _),fun c hc Tstar hT Ω' _ P' B hB => ?_⟩
  have hc₁' := (le_max_left c₁ c₂).trans_lt hc
  have hc₂' := (le_max_right c₁ c₂).trans_lt hc
  exact threshold_state_coupling_from_limits M c (hc₁.trans hc₁') Tstar hT
    (hResidual c hc₁' Tstar hT) (hFluid c hc₂' Tstar hT) Ω' P' B hB
