-- Prove2me | solution 1 for BanditAlgorithm.tendsto_gittins_terminal_retirement_potential_zero
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-01T17:15:17.918543+00:00
-- url     : https://prove2.me/submissions/7f713350-5a8f-4cba-bcf6-9945085125d6

import Theorems.Thm_BanditAlgorithm_gittins_expected_terminal_potential_nonneg
import Theorems.Thm_BanditAlgorithm_gittins_expected_terminal_potential_le_stack_envelope
import Theorems.Thm_BanditAlgorithm_tendsto_gittins_stack_retirement_envelope_zero

open MeasureTheory ProbabilityTheory ENNReal

theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : BanditAlgorithm.DiscountedRewardIntegrable P r α)
    (π : BanditAlgorithm.MarkovBanditPolicy k S) (x : Fin k → S) :
    Filter.Tendsto (fun N ↦ α ^ N *
      BanditAlgorithm.markovBanditExpectedRetirementPotential P r α π x N)
      Filter.atTop (nhds 0) := by
  let absoluteValue := fun y : S ↦
    ∫ path, ∑' t : ℕ, α ^ t * |r (path t)|
      ∂BanditAlgorithm.markovChainMeasure P y
  let envelope := fun (N : ℕ) (ω : Fin k → ℕ → S) ↦ ∑ i : Fin k,
    ((∑ u ∈ Finset.range (N + 1), absoluteValue (ω i u)) +
      (∑' t : ℕ, α ^ t) *
        (absoluteValue (ω i 0) +
          ∑ v ∈ Finset.range N, |r (ω i (v + 1))|))
  let stackMeasure : Measure (Fin k → ℕ → S) :=
    Measure.pi (fun i ↦ BanditAlgorithm.markovChainMeasure P (x i))
  let upper : ℕ → ℝ := fun N ↦ α ^ N *
    ∫ ω, envelope N ω ∂stackMeasure
  apply squeeze_zero' (g := upper)
  · exact Filter.Eventually.of_forall fun N ↦
      mul_nonneg (pow_nonneg hα0.le N)
        (BanditAlgorithm.gittins_expected_terminal_potential_nonneg
          P hr hα0 hα1 hint π x N)
  · exact Filter.Eventually.of_forall fun N ↦ by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hα0.le N)
      exact BanditAlgorithm.gittins_expected_terminal_potential_le_stack_envelope
        P hr hα0 hα1 hint π x
  · exact BanditAlgorithm.tendsto_gittins_stack_retirement_envelope_zero
      P hr hα0 hα1 hint x
