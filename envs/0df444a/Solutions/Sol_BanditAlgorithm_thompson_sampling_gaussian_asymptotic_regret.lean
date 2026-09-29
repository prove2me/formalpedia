-- Prove2me | solution 1 for BanditAlgorithm.thompson_sampling_gaussian_asymptotic_regret
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T22:20:18.210657+00:00
-- url     : https://prove2.me/submissions/892866e8-ef2d-4690-b27c-f2ce181a6c69

import Theorems.Thm_BanditAlgorithm_bandit_regret_decomposition
import Theorems.Thm_BanditAlgorithm_gaussian_ts_suboptimal_pull_count_asymptotic
import Mathlib.Probability.Distributions.Gaussian.Fernique

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace BanditAlgorithm

theorem _root_.solution :
    ∀ (k : ℕ) [NeZero k] (μvec : Fin k → ℝ) (π : BanditPolicy k),
      IsGaussianTSPolicy π →
      Tendsto (fun n : ℕ ↦ banditRegret (gaussianBandit μvec) π n / Real.log n)
        atTop
        (nhds (∑ i ∈ Finset.univ.filter
            (fun i ↦ 0 < banditGap (gaussianBandit μvec) i),
          2 / banditGap (gaussianBandit μvec) i)) := by
  intro k _ μvec π hπ
  let ν := gaussianBandit μvec
  change
    Tendsto (fun n : ℕ ↦ banditRegret ν π n / Real.log n) atTop
      (nhds (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        2 / banditGap ν i))
  have hInt : ∀ i, Integrable id (ν.P i) := by
    intro i
    change Integrable id (gaussianReal (μvec i) 1)
    exact IsGaussian.integrable_id
  have hrewrite (n : ℕ) :
      banditRegret ν π n / Real.log n =
        ∑ i ∈ Finset.univ,
          banditGap ν i *
            ((∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) /
              Real.log n) := by
    rw [bandit_regret_decomposition ν hInt π n, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hlim :
      Tendsto
        (fun n : ℕ ↦
          ∑ i ∈ Finset.univ,
            banditGap ν i *
              ((∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) /
                Real.log n))
        atTop
        (nhds
          (∑ i ∈ Finset.univ,
            if 0 < banditGap ν i then 2 / banditGap ν i else 0)) := by
    apply tendsto_finset_sum
    intro i _
    by_cases hi : 0 < banditGap ν i
    · simp only [hi, if_true]
      convert
        (gaussian_ts_suboptimal_pull_count_asymptotic μvec π hπ i hi).const_mul
          (banditGap ν i) using 1
      change nhds (2 / banditGap ν i) =
        nhds (banditGap ν i * (2 / banditGap ν i ^ 2))
      congr 1
      field_simp [ne_of_gt hi]
      <;> ring
    · have hgap_nonneg : 0 ≤ banditGap ν i := by
        rw [banditGap]
        exact sub_nonneg.mpr
          (le_ciSup (Finite.bddAbove_range (fun j ↦ banditArmMean ν j)) i)
      have hgapzero : banditGap ν i = 0 :=
        le_antisymm (le_of_not_gt hi) hgap_nonneg
      simp [hi, hgapzero]
  simpa only [hrewrite, Finset.sum_filter] using hlim

end BanditAlgorithm
