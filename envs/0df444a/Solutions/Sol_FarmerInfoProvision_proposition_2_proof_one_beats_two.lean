-- Prove2me | solution 1 for FarmerInfoProvision.proposition_2_proof_one_beats_two
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T02:32:11.50868+00:00
-- url     : https://prove2.me/submissions/d8a75b27-a6c5-40d0-ad3e-d536c74e73c4

import Mathlib
import Definitions.Def_FarmerInfoProvision_Psi
import Definitions.Def_FarmerInfoProvision_totalWelfare

set_option maxHeartbeats 4000000 in
open FarmerInfoProvision in
theorem solution {n : ℕ} (hn : 4 ≤ n) {a b c α β γ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hα : 0 < α) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    totalWelfare a b c (n : ℝ) 1 α β γ - totalWelfare a b c (n : ℝ) 2 α β γ =
      β * (64 * α ^ 6 + 64 * α ^ 5 * (3 * β + 4 * (n : ℝ) * γ) +
        (1 + (n : ℝ)) * γ ^ 3 * (β + γ) * (4 * (-3 + (n : ℝ)) * β ^ 2 +
          4 * (-5 + 3 * (n : ℝ)) * β * γ + (-5 + 7 * (n : ℝ)) * γ ^ 2) +
        16 * α ^ 4 * (12 * β ^ 2 + (-1 + 33 * (n : ℝ)) * β * γ +
          (-15 + 34 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * γ ^ 2) +
        4 * α * γ ^ 2 * (4 * (-4 + (n : ℝ)) * β ^ 3 +
          2 * (-25 + 4 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * β ^ 2 * γ +
          (-47 + 11 * (n : ℝ) + 29 * (n : ℝ) ^ 2) * β * γ ^ 2 +
          2 * (-6 + 4 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * γ ^ 3) +
        32 * α ^ 3 * (2 * β ^ 3 + (-1 + 9 * (n : ℝ)) * β ^ 2 * γ +
          (-16 + 25 * (n : ℝ) + 5 * (n : ℝ) ^ 2) * β * γ ^ 2 +
          (-10 + 14 * (n : ℝ) + 7 * (n : ℝ) ^ 2) * γ ^ 3) +
        4 * α ^ 2 * γ * (4 * (-1 + (n : ℝ)) * β ^ 3 +
          4 * (-21 + 17 * (n : ℝ) + 3 * (n : ℝ) ^ 2) * β ^ 2 * γ +
          (-126 + 95 * (n : ℝ) + 59 * (n : ℝ) ^ 2) * β * γ ^ 2 +
          (-45 + 44 * (n : ℝ) + 42 * (n : ℝ) ^ 2) * γ ^ 3)) /
      (b * (Psi (n : ℝ) 1 α β γ / 2) ^ 2 * Psi (n : ℝ) 2 α β γ ^ 2) ∧
    totalWelfare a b c (n : ℝ) 2 α β γ < totalWelfare a b c (n : ℝ) 1 α β γ := by
  generalize hNdef : (n : ℝ) = N
  have hN : (4 : ℝ) ≤ N := by rw [← hNdef]; exact_mod_cast hn
  have hP1 : 0 < Psi N 1 α β γ := by unfold Psi; positivity
  have hP2 : 0 < Psi N 2 α β γ := by unfold Psi; positivity
  have hDEN : 0 < b * (Psi N 1 α β γ / 2) ^ 2 * Psi N 2 α β γ ^ 2 := by positivity
  have hb0 := hb.ne'
  have hα0 := hα.ne'
  have hβ0 := hβ.ne'
  have hN1 : N + 1 ≠ 0 := by linarith
  have hP10 := hP1.ne'
  have hP20 := hP2.ne'
  have key : totalWelfare a b c N 1 α β γ - totalWelfare a b c N 2 α β γ =
          β * (64 * α ^ 6 + 64 * α ^ 5 * (3 * β + 4 * N * γ) +
            (1 + N) * γ ^ 3 * (β + γ) * (4 * (-3 + N) * β ^ 2 +
              4 * (-5 + 3 * N) * β * γ + (-5 + 7 * N) * γ ^ 2) +
            16 * α ^ 4 * (12 * β ^ 2 + (-1 + 33 * N) * β * γ +
              (-15 + 34 * N + 7 * N ^ 2) * γ ^ 2) +
            4 * α * γ ^ 2 * (4 * (-4 + N) * β ^ 3 +
              2 * (-25 + 4 * N + 7 * N ^ 2) * β ^ 2 * γ +
              (-47 + 11 * N + 29 * N ^ 2) * β * γ ^ 2 +
              2 * (-6 + 4 * N + 7 * N ^ 2) * γ ^ 3) +
            32 * α ^ 3 * (2 * β ^ 3 + (-1 + 9 * N) * β ^ 2 * γ +
              (-16 + 25 * N + 5 * N ^ 2) * β * γ ^ 2 +
              (-10 + 14 * N + 7 * N ^ 2) * γ ^ 3) +
            4 * α ^ 2 * γ * (4 * (-1 + N) * β ^ 3 +
              4 * (-21 + 17 * N + 3 * N ^ 2) * β ^ 2 * γ +
              (-126 + 95 * N + 59 * N ^ 2) * β * γ ^ 2 +
              (-45 + 44 * N + 42 * N ^ 2) * γ ^ 3)) /
          (b * (Psi N 1 α β γ / 2) ^ 2 * Psi N 2 α β γ ^ 2) := by
    rcases eq_or_lt_of_le hγ with h0 | hγpos
    · subst h0
      unfold totalWelfare profitInformed profitUninformed coefA0 coefA1 coefA2 coefB1
      rw [eq_div_iff hDEN.ne']
      field_simp
      unfold Psi
      ring
    · have hγ0 := hγpos.ne'
      unfold totalWelfare profitInformed profitUninformed coefA0 coefA1 coefA2 coefB1
      rw [eq_div_iff hDEN.ne']
      field_simp
      unfold Psi
      ring
  refine ⟨key, ?_⟩
  have hpos : 0 < totalWelfare a b c N 1 α β γ - totalWelfare a b c N 2 α β γ := by
    rw [key]
    apply div_pos _ hDEN
    obtain ⟨t, ht, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ N = 4 + t := ⟨N - 4, by linarith, by ring⟩
    ring_nf
    positivity
  linarith
