-- Prove2me | solution 1 for BanditAlgorithm.gaussian_ts_suboptimal_pull_count_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T01:34:58.135047+00:00
-- url     : https://prove2.me/submissions/50114d51-dc2b-4ef8-9ced-9264ab119f1c

import Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_eventual_lower
import Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_eventual_upper

open MeasureTheory ProbabilityTheory Filter

theorem solution
    {k : ℕ} [NeZero k] (μvec : Fin k → ℝ)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsGaussianTSPolicy π) (i : Fin k)
    (hi : 0 < BanditAlgorithm.banditGap
      (BanditAlgorithm.gaussianBandit μvec) i) :
    Tendsto
      (fun n : ℕ ↦
        (∫ h, (BanditAlgorithm.armPullCount i h : ℝ)
          ∂BanditAlgorithm.banditMeasure
            (BanditAlgorithm.gaussianBandit μvec) π n) / Real.log n)
      atTop
      (nhds (2 / BanditAlgorithm.banditGap
        (BanditAlgorithm.gaussianBandit μvec) i ^ 2)) := by
  exact tendsto_order.2
    ⟨BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_lower
        μvec π hπ i hi,
      BanditAlgorithm.gaussian_ts_suboptimal_pull_count_eventual_upper
        μvec π hπ i hi⟩
