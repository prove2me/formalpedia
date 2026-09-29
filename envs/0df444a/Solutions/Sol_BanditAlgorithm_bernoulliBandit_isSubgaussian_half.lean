-- Prove2me | solution 1 for BanditAlgorithm.bernoulliBandit_isSubgaussian_half
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T04:32:59.578318+00:00
-- url     : https://prove2.me/submissions/5b8dd9e7-1ccf-479c-8e06-ae59f7b3cad5

import Definitions.Def_bernoulliRelativeEntropy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

private theorem bernoulliBandit_ae_mem_Icc_half
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    ∀ᵐ x ∂(bernoulliBandit μvec hμ).P i, x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [bernoulliBandit, MeasureTheory.ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simp) _
  · exact Measure.ae_smul_measure (by simp) _

end BanditAlgorithm

theorem solution
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) :
    BanditAlgorithm.IsSubgaussianBandit (1 / 2)
      (BanditAlgorithm.bernoulliBandit μvec hμ) := by
  constructor
  · intro i
    exact Integrable.of_mem_Icc 0 1 measurable_id.aemeasurable
      (BanditAlgorithm.bernoulliBandit_ae_mem_Icc_half μvec hμ i)
  · intro i
    have hsg :=
      ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc
        (μ := (BanditAlgorithm.bernoulliBandit μvec hμ).P i)
        (X := id) measurable_id.aemeasurable
        (BanditAlgorithm.bernoulliBandit_ae_mem_Icc_half μvec hμ i)
    simpa [BanditAlgorithm.banditArmMean] using hsg
