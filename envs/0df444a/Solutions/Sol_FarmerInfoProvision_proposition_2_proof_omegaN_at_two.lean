-- Prove2me | solution 1 for FarmerInfoProvision.proposition_2_proof_omegaN_at_two
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T08:55:53.315989+00:00
-- url     : https://prove2.me/submissions/59269b1c-e289-49f4-a60f-b9ec2fbe9983

import Mathlib
import Definitions.Def_FarmerInfoProvision_OmegaN

open FarmerInfoProvision in
theorem solution {n : ℕ} (hn : 3 ≤ n) {α β γ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    OmegaN (n : ℝ) 2 α β γ =
      -4 * β * (16 * α ^ 4 + 8 * α ^ 3 * (4 * β + (1 + 4 * (n : ℝ)) * γ) +
        γ ^ 2 * (2 * (-3 + (n : ℝ)) * β ^ 2 + (-9 + 7 * (n : ℝ)) * β * γ +
          2 * (-1 + 2 * (n : ℝ)) * γ ^ 2) +
        4 * α ^ 2 * (4 * β ^ 2 + (3 + 8 * (n : ℝ)) * β * γ + 3 * (-1 + 4 * (n : ℝ)) * γ ^ 2) +
        2 * α * γ * (2 * β ^ 2 + (-10 + 15 * (n : ℝ)) * β * γ +
          (-5 + 12 * (n : ℝ)) * γ ^ 2)) ∧
    OmegaN (n : ℝ) 2 α β γ < 0 := by
  have h1 : OmegaN (n : ℝ) 2 α β γ =
      -4 * β * (16 * α ^ 4 + 8 * α ^ 3 * (4 * β + (1 + 4 * (n : ℝ)) * γ) +
        γ ^ 2 * (2 * (-3 + (n : ℝ)) * β ^ 2 + (-9 + 7 * (n : ℝ)) * β * γ +
          2 * (-1 + 2 * (n : ℝ)) * γ ^ 2) +
        4 * α ^ 2 * (4 * β ^ 2 + (3 + 8 * (n : ℝ)) * β * γ + 3 * (-1 + 4 * (n : ℝ)) * γ ^ 2) +
        2 * α * γ * (2 * β ^ 2 + (-10 + 15 * (n : ℝ)) * β * γ +
          (-5 + 12 * (n : ℝ)) * γ ^ 2)) := by
    unfold OmegaN
    ring
  refine ⟨h1, ?_⟩
  have hn' : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  obtain ⟨a, ha, hna⟩ : ∃ a : ℝ, 0 ≤ a ∧ (n : ℝ) = a + 3 := ⟨n - 3, by linarith, by ring⟩
  rw [h1, hna]
  apply mul_neg_of_neg_of_pos (by linarith)
  ring_nf
  positivity
