-- Prove2me | solution 1 for BanditAlgorithm.mdp_ucrl2_regret_bound_known_reward_diam_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T20:00:20.453443+00:00
-- url     : https://prove2.me/submissions/f6f632e0-7416-4ab4-9156-6b29002b1c25

import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one
import Theorems.Thm_BanditAlgorithm_mdp_ucrl2_expected_regret_known_reward_diam_ge_one

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      (∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) 1 →
          ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
            ∃ π : MDPPolicy S A,
              ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
                1 ≤ mdpDiameter M →
                ∀ μ0 : MDPStateDistribution S,
                  mdpMeasure M μ0 π n
                      {h | C * mdpDiameter M * S *
                          Real.sqrt (A * n * Real.log (n * S * A / δ)) ≤
                        mdpRegret M n h} ≤
                    ENNReal.ofReal δ) ∧
      (∀ S A n : ℕ, 0 < S → 0 < A → 0 < n →
        ∀ r : Fin S → Fin A → ℝ, (∀ s a, r s a ∈ Set.Icc (0 : ℝ) 1) →
          ∃ π : MDPPolicy S A,
            ∀ M : FiniteMDP S A, M.r = r → M.IsCommunicating →
              1 ≤ mdpDiameter M →
              ∀ μ0 : MDPStateDistribution S,
                ∫ h, mdpRegret M n h ∂(mdpMeasure M μ0 π n) ≤
                  1 + C * mdpDiameter M * S *
                    Real.sqrt (2 * A * n * Real.log n)) := by
  obtain ⟨C₁, hC₁, hhigh⟩ :=
    mdp_ucrl2_high_probability_regret_known_reward_diam_ge_one
  obtain ⟨C₂, hC₂, hexpect⟩ :=
    mdp_ucrl2_expected_regret_known_reward_diam_ge_one
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_, ?_⟩
  · intro S A n hS hA hn δ hδ r hr
    obtain ⟨π, hπ⟩ := hhigh S A n hS hA hn δ hδ r hr
    refine ⟨π, fun M hMr hcomm hdiam μ0 ↦ ?_⟩
    refine (measure_mono ?_).trans (hπ M hMr hcomm hdiam μ0)
    intro h hh
    change max C₁ C₂ * mdpDiameter M * (S : ℝ) *
        Real.sqrt ((A : ℝ) * n * Real.log ((n : ℝ) * S * A / δ)) ≤
          mdpRegret M n h at hh
    change C₁ * mdpDiameter M * (S : ℝ) *
        Real.sqrt ((A : ℝ) * n * Real.log ((n : ℝ) * S * A / δ)) ≤
          mdpRegret M n h
    apply le_trans ?_ hh
    gcongr
    exact le_max_left _ _
  · intro S A n hS hA hn r hr
    obtain ⟨π, hπ⟩ := hexpect S A n hS hA hn r hr
    refine ⟨π, fun M hMr hcomm hdiam μ0 ↦
      (hπ M hMr hcomm hdiam μ0).trans ?_⟩
    gcongr
    exact le_max_right _ _
