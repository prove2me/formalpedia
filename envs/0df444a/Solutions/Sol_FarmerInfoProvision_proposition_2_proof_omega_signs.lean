-- Prove2me | solution 1 for FarmerInfoProvision.proposition_2_proof_omega_signs
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:04:03.805259+00:00
-- url     : https://prove2.me/submissions/69fdc93a-6dcb-4eb3-a647-fefe26930273

import Mathlib
import Definitions.Def_FarmerInfoProvision_OmegaN
import Definitions.Def_FarmerInfoProvision_OmegaD

open FarmerInfoProvision in
theorem solution {n : ℕ} (hn : 4 ≤ n) {b α β γ : ℝ}
    (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    (∀ t : ℝ, 0 < t → 0 < OmegaD b (n : ℝ) t α β γ) ∧
    ∃ k₀ k₁ : ℝ, k₁ < 0 ∧ ∀ t : ℝ, OmegaN (n : ℝ) t α β γ = k₀ + k₁ * t := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨fun t ht => ?_, ?_⟩
  · unfold OmegaD
    have hX : 0 < 4 * (1 + t) * α ^ 2 + (1 + (n : ℝ)) * γ * (2 * β + γ + t * γ) +
        2 * (1 + t) * α * (2 * β + (2 + (n : ℝ)) * γ) := by positivity
    positivity
  · refine ⟨OmegaN (n : ℝ) 0 α β γ,
      -4 * β * (16 * α ^ 4 + 8 * α ^ 3 * (4 * β + (3 + 2 * (n : ℝ)) * γ) +
        γ ^ 2 * ((3 * (n : ℝ) - 1) * β * γ + 2 * (n : ℝ) * γ ^ 2) +
        4 * α ^ 2 * (4 * β ^ 2 + (9 + 4 * (n : ℝ)) * β * γ + 3 * (1 + 2 * (n : ℝ)) * γ ^ 2) +
        2 * α * γ * (6 * β ^ 2 + (4 + 7 * (n : ℝ)) * β * γ + (1 + 6 * (n : ℝ)) * γ ^ 2)),
      ?_, fun t => ?_⟩
    · have e1 : 0 < 16 * α ^ 4 := by positivity
      have e2 : 0 ≤ 8 * α ^ 3 * (4 * β + (3 + 2 * (n : ℝ)) * γ) := by positivity
      have h3 : 0 ≤ 3 * (n : ℝ) - 1 := by linarith
      have e3 : 0 ≤ γ ^ 2 * ((3 * (n : ℝ) - 1) * β * γ + 2 * (n : ℝ) * γ ^ 2) :=
        mul_nonneg (by positivity)
          (add_nonneg (mul_nonneg (mul_nonneg h3 hβ.le) hγ) (by positivity))
      have e4 : 0 ≤ 4 * α ^ 2 * (4 * β ^ 2 + (9 + 4 * (n : ℝ)) * β * γ +
          3 * (1 + 2 * (n : ℝ)) * γ ^ 2) := by positivity
      have e5 : 0 ≤ 2 * α * γ * (6 * β ^ 2 + (4 + 7 * (n : ℝ)) * β * γ +
          (1 + 6 * (n : ℝ)) * γ ^ 2) := by positivity
      have hE : 0 < 16 * α ^ 4 + 8 * α ^ 3 * (4 * β + (3 + 2 * (n : ℝ)) * γ) +
        γ ^ 2 * ((3 * (n : ℝ) - 1) * β * γ + 2 * (n : ℝ) * γ ^ 2) +
        4 * α ^ 2 * (4 * β ^ 2 + (9 + 4 * (n : ℝ)) * β * γ + 3 * (1 + 2 * (n : ℝ)) * γ ^ 2) +
        2 * α * γ * (6 * β ^ 2 + (4 + 7 * (n : ℝ)) * β * γ + (1 + 6 * (n : ℝ)) * γ ^ 2) := by
        linarith
      have h4 : -4 * β < 0 := by linarith
      exact mul_neg_of_neg_of_pos h4 hE
    · unfold OmegaN
      ring
