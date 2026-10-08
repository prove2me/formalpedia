-- Prove2me | solution 1 for ConnesGreen.actual_zero_negative_form_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T06:41:39.946114+00:00
-- url     : https://prove2.me/submissions/9a7f70f4-dbff-4fc7-bcda-5276a4041a56

import Theorems.Thm_ConnesGreen_actual_zero_half_bound_iff_finite_restoration
import Theorems.Thm_WeilDefect_MarkerStability_negative_form_small_regularization
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder

noncomputable section
theorem solution (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) :
    ∃ P : ℓ²(CriticalZeros, ℂ) →L[ℂ] Physical t,
    ∃ M : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] Physical t,
      (∀ ρ, P (lp.single 2 ρ (1 : ℂ)) =
        positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ) ∧
      (∀ ρ, M (lp.single 2 ρ (1 : ℂ)) =
        negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) ∧
      (∀ x : Physical t, ‖P.adjoint x‖ ^ 2 - ‖M.adjoint x‖ ^ 2 < 0 →
        ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
          ∃ α : ℝ, 0 < α ∧ α < 1 ∧ ∀ F : Finset CriticalZeros, S ⊆ F →
            ∀ B : ℓ²({ρ : CriticalZeros // ρ ∉ F}, ℂ) →L[ℂ] Physical t,
              (∀ ρ, B (lp.single 2 ρ (1 : ℂ)) =
                negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1) →
              ‖B ∘L B.adjoint‖ ≤ α * ε →
              ¬ (1 / 2 - α) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
                ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤
                marker (P ∘L P.adjoint + ε • 1 - B ∘L B.adjoint) M) := by
  obtain ⟨P, M, hP, hM, hiff⟩ := actual_zero_half_bound_iff_finite_restoration t ht S
  refine ⟨P, M, hP, hM, ?_⟩
  intro x hn
  obtain ⟨δ, hδ, hfailure⟩ := negative_form_small_regularization P M x hn
  refine ⟨δ, hδ, ?_⟩
  intro ε hε heδ
  have hnot := mt (hiff ε hε).mpr (hfailure ε hε heδ)
  push_neg at hnot
  exact hnot
