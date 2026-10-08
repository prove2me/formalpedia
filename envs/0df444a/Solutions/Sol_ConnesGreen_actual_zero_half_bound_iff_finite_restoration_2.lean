-- Prove2me | solution 2 for ConnesGreen.actual_zero_half_bound_iff_finite_restoration
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T16:43:12.17607+00:00
-- url     : https://prove2.me/submissions/9650db39-2381-4bf5-8611-78391ab8b767

import Theorems.Thm_ConnesGreen_actual_zero_lower_bound_iff_finite_restoration
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability Filter
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section

theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ ε : ℝ, 0 < ε →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
          ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (P ∘L P.adjoint + ε • 1) M ↔
        ∀ α : ℝ, 0 < α → α < 1 →
          ∃ F : Finset CriticalZeros, S ⊆ F ∧
          ∃ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
            (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
              negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
            ‖B ∘L B.adjoint‖ ≤ α * ε ∧
            (1 / 2 - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
              ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤
              marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M))  := by
  obtain ⟨P, M, hP, hM, hrec⟩ := ConnesGreen.actual_zero_lower_bound_iff_finite_restoration t ht S
  exact ⟨P, M, hP, hM, fun ε hε => hrec ε hε (1 / 2)⟩
