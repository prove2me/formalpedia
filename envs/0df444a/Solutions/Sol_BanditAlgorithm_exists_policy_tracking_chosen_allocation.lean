-- Prove2me | solution 1 for BanditAlgorithm.exists_policy_tracking_chosen_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T05:32:11.375387+00:00
-- url     : https://prove2.me/submissions/1136a905-8eea-44ab-8910-e8047ee743e2

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Theorems.Thm_BanditAlgorithm_exists_policy_tracking_optimal_allocation
import Theorems.Thm_BanditAlgorithm_gaussian_optimal_allocation_unique

open MeasureTheory ProbabilityTheory InformationTheory NNReal ENNReal Filter

theorem _root_.solution {k : ℕ} [NeZero k]
    (choice : (Fin k → ℝ) → Fin k → NNReal)
    (hchoice : ∀ μvec : Fin k → ℝ, (∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar) →
      (∀ i, 0 < choice μvec i) ∧
        BanditAlgorithm.IsOptimalAllocation (BanditAlgorithm.gaussianBandit μvec)
          (Set.range (BanditAlgorithm.gaussianBandit (k := k))) (choice μvec)) :
    ∃ pol : BanditAlgorithm.BanditPolicy k, ∀ μvec : Fin k → ℝ,
      (∃ istar : Fin k, ∀ j, j ≠ istar → μvec j < μvec istar) →
      ∀ᵐ ω ∂(BanditAlgorithm.banditTrajMeasure
          (BanditAlgorithm.gaussianBandit μvec) pol), ∀ i : Fin k,
        Filter.Tendsto (fun t : ℕ ↦ BanditAlgorithm.trajAllocation i t ω) Filter.atTop
          (nhds ((choice μvec i : ℝ))) := by
  obtain ⟨pol, hpol⟩ :=
    BanditAlgorithm.exists_policy_tracking_optimal_allocation (k := k)
  refine ⟨pol, fun μvec hstar ↦ ?_⟩
  obtain ⟨α, hαopt, hα⟩ := hpol μvec hstar
  obtain ⟨istar, hs⟩ := hstar
  have heq : α = choice μvec :=
    BanditAlgorithm.gaussian_optimal_allocation_unique hs hαopt
      (hchoice μvec ⟨istar, hs⟩).2
  rwa [heq] at hα
