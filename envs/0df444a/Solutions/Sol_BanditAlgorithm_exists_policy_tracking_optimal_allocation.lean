-- Prove2me | solution 1 for BanditAlgorithm.exists_policy_tracking_optimal_allocation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:27:41.091001+00:00
-- url     : https://prove2.me/submissions/bc568efb-791f-49a6-985b-3c5a0ce8892d

import Mathlib
import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Theorems.Thm_BanditAlgorithm_exists_policy_optimal_allocation_with_integrable_settling_time

set_option autoImplicit false

open MeasureTheory Filter Topology

private theorem ae_allocation_convergence
    {A I : Type*} [MeasurableSpace A] (P : Measure A)
    (f : I → ℕ → A → ℝ) (a : I → ℝ)
    (h : ∀ e : ℝ, 0 < e → ∀ᵐ w ∂P,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ i, |f i n w - a i| ≤ e) :
    ∀ᵐ w ∂P, ∀ i, Tendsto (fun n : ℕ => f i n w) atTop (𝓝 (a i)) := by
  have he : ∀ᵐ w ∂P, ∀ j : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ i, |f i n w - a i| ≤ 1 / ((j : ℝ) + 1) := by
    exact ae_all_iff.mpr fun j => h _ (by positivity)
  filter_upwards [he] with w hw
  intro i
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt he
  obtain ⟨N, hN⟩ := hw j
  refine ⟨N, fun n hn => ?_⟩
  simpa only [Real.dist_eq] using lt_of_le_of_lt (hN n hn i) hj

-- The accepted stronger result supplies a single policy and eventual accuracy
-- at each positive tolerance. Only a countable intersection is needed here.
-- Provenance: Grace, accepted submission 53f696fd-7a86-4e85-84b9-d1dd1adf6f09.
theorem solution {k : ℕ} [NeZero k] :
    ∃ pol : BanditAlgorithm.BanditPolicy k, ∀ μvec : Fin k → ℝ,
      (∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar) →
      ∃ α : Fin k → NNReal,
        BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
            (Set.range (BanditAlgorithm.gaussianBandit (k := k))) α ∧
          ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
              (BanditAlgorithm.gaussianBandit μvec) pol), ∀ i : Fin k,
            Filter.Tendsto (fun t : ℕ ↦ BanditAlgorithm.trajAllocation i t ω)
              Filter.atTop (nhds ((α i : ℝ))) := by
  obtain ⟨pol, hpol⟩ :=
    BanditAlgorithm.exists_policy_optimal_allocation_with_integrable_settling_time (k := k)
  refine ⟨pol, ?_⟩
  intro μvec hbest
  obtain ⟨istar, hstar⟩ := hbest
  obtain ⟨α, _hpositive, hoptimal, hsettle⟩ := hpol μvec istar hstar
  refine ⟨α, hoptimal, ?_⟩
  apply ae_allocation_convergence
  intro e he
  filter_upwards [(hsettle e he).1] with ω hω
  obtain ⟨N, hN⟩ := hω
  exact ⟨N, fun n hn => (hN n hn).2.1⟩
