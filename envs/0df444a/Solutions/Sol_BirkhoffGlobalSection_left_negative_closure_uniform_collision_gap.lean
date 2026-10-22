-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_uniform_collision_gap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:09:24.317145+00:00
-- url     : https://prove2.me/submissions/6b020cab-e03a-4655-97df-b45c138a06b7

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_position_radius_lt_one

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))),
        δ ≤ secondCollisionDistanceSq s := by
  obtain ⟨ρ, hρ, hbound⟩ :=
    left_negative_closure_position_radius_lt_one μ c hμ0 hμ1 hc
  refine ⟨((1 - ρ) / 2) ^ 2, ?_, ?_⟩
  · have hp : 0 < (1 - ρ) / 2 := by linarith
    positivity
  intro s hs
  let u : ℝ := 2 * (s 0 ^ 2 - s 1 ^ 2)
  let v : ℝ := 4 * s 0 * s 1
  have hf :
      ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
        ((leviCivitaPosition μ s) 1) ^ 2 = u ^ 2 + v ^ 2 := by
    dsimp [leviCivitaPosition, u, v]
    ring
  have hbound' : u ^ 2 + v ^ 2 ≤ ρ := by
    rw [← hf]
    exact hbound s hs
  have hu : u ≤ (ρ + 1) / 2 := by
    nlinarith [sq_nonneg (u - 1), sq_nonneg v]
  have hleft : 0 ≤ (1 - u) - (1 - ρ) / 2 := by linarith
  have hright : 0 ≤ (1 - u) + (1 - ρ) / 2 := by linarith
  have hprod := mul_nonneg hleft hright
  change ((1 - ρ) / 2) ^ 2 ≤ (u - 1) ^ 2 + v ^ 2
  nlinarith [hprod, sq_nonneg v]
