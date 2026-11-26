-- Prove2me | solution 1 for BellWilliams2001.ThresholdPolicy.threshold_policy_asymptotically_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T05:35:47.094691+00:00
-- url     : https://prove2.me/submissions/971bfbe9-ccb9-4afc-b4b0-69c7e026abbc
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BellWilliams2001_ThresholdPolicy_state_space_collapse
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_fluid_limit_of_finite_cost
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_queue_second_moment
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_discounted_cost_of_queue_coupling
import Theorems.Thm_BellWilliams2001_ThresholdPolicy_workload_lower_bound_on_fluid_subsequence

open BellWilliams2001.ThresholdPolicy
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ Tstar : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (Tstar n) ∧ M.IsThreshold c n (Tstar n)) →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : Fin 2 → ℝ≥0 → Ω' → ℝ),
        IsBrownianPair P' B →
        (∀ T : ℕ → Allocation Ω, (∀ n, M.IsAdmissible n (T n)) →
          M.Jstar P' B ≤ liminf (fun n => M.cost n (T n)) atTop) ∧
        Tendsto (fun n => M.cost n (Tstar n)) atTop (𝓝 (M.Jstar P' B)) ∧
        M.Jstar P' B < ⊤ := by
  obtain ⟨c₁, hc₁, hcollapse⟩ := state_space_collapse M
  obtain ⟨c₂, _, hmom⟩ := threshold_queue_second_moment M
  refine ⟨max c₁ c₂, hc₁.trans_le (le_max_left _ _), ?_⟩
  intro c hc Tstar hT Ω' mΩ' P' B hB
  have hc1 := (le_max_left c₁ c₂).trans_lt hc
  have hc2 := (le_max_right c₁ c₂).trans_lt hc
  refine ⟨?_, ?_⟩
  · intro T hAdmissible
    by_cases hfin : liminf (fun n => M.cost n (T n)) atTop < ⊤
    · obtain ⟨ψ, hψ, hψTop⟩ := exists_seq_tendsto_liminf
        (u := fun n => M.cost n (T n)) (f := atTop)
      obtain ⟨k, hk, hφ⟩ := strictMono_subseq_of_tendsto_atTop hψTop
      have hlim : Tendsto (fun n => M.cost ((ψ ∘ k) n) (T ((ψ ∘ k) n))) atTop
          (𝓝 (liminf (fun n => M.cost n (T n)) atTop)) := hψ.comp hk.tendsto_atTop
      have hfluid := (fluid_limit_of_finite_cost M T hAdmissible hfin (ψ ∘ k) hφ hlim).2.2.2.1
      have hlower := workload_lower_bound_on_fluid_subsequence M T hAdmissible
        (ψ ∘ k) hφ hfluid Ω' P' B hB
      rwa [hlim.liminf_eq] at hlower
    · rw [top_le_iff.1 (le_of_not_gt hfin)]
      exact le_top
  · have hlarge : ∀ᶠ n in atTop, 1 ≤ M.threshold c n := by
      have h := (Real.tendsto_log_atTop.comp M.r_tendsto).const_mul_atTop (hc₁.trans hc1)
      filter_upwards [h.eventually_ge_atTop (1 : ℝ)] with n hn
      exact (Nat.one_le_floor_iff _).mpr hn
    obtain ⟨C, hC, p, hMom⟩ := hmom c hc2 Tstar hT
    exact discounted_cost_of_queue_coupling M Tstar (hlarge.mono fun n hn => (hT n hn).1)
      Ω' P' B hB (hcollapse c hc1 Tstar hT Ω' P' B hB) C hC p hMom
