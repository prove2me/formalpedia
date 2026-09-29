-- Prove2me | solution 1 for BanditAlgorithm.gittins_policy_dominates_of_epsilon_stopping_calibration
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T16:29:34.032107+00:00
-- url     : https://prove2.me/submissions/a774e48b-1057-433d-92de-0ea1d0318c8f

import Theorems.Thm_BanditAlgorithm_gittins_ae_discounted_value_interleaving_certificates
import Theorems.Thm_BanditAlgorithm_le_of_ae_discounted_permutation_approximations

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem solution
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (hcal : ∀ (y : S) (ε : ℝ), 0 < ε →
      ∃ τ : (ℕ → S) → ℕ∞,
        IsTrajStoppingTime τ ∧ (∀ ω, 1 ≤ τ ω) ∧
        gittinsIndex P r α y - ε <
          (∫ ω, discountedStoppedSum α r τ ω ∂markovChainMeasure P y) /
            (∫ ω, discountedStoppedSum α (fun _ ↦ 1) τ ω
              ∂markovChainMeasure P y))
    (πstar : MarkovBanditPolicy k S)
    (hπ : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) :
    ∀ π : MarkovBanditPolicy k S,
      markovBanditDiscountedValue P r α π x ≤
        markovBanditDiscountedValue P r α πstar x := by
  intro π
  obtain ⟨μ, hcert⟩ :=
    gittins_ae_discounted_value_interleaving_certificates
      P hr hα0 hα1 hint hcal πstar hπ x π
  exact le_of_ae_discounted_permutation_approximations
    μ hα0.le hα1.le hcert
