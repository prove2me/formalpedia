-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_second_collision_separated
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T08:25:07.737858+00:00
-- url     : https://prove2.me/submissions/c127e625-e202-4468-b6bb-73d379cb3b28

import Mathlib.Tactic
import Theorems.Thm_BirkhoffGlobalSection_left_component_position_radius_lt_one

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ leftEnergyComponent μ c,
      δ ≤ Real.sqrt (secondCollisionDistanceSq s) := by
  obtain ⟨ρ, hρ, hb⟩ := left_component_position_radius_lt_one μ c hμ0 hμ1 hc
  refine ⟨(1 - ρ) / 2, by linarith, ?_⟩
  intro s hs
  let a : ℝ := (leviCivitaPosition μ s) 0 + μ
  let b : ℝ := (leviCivitaPosition μ s) 1
  have hrad : a ^ 2 + b ^ 2 ≤ ρ := by simpa only [a, b] using hb s hs
  have ha : (1 - ρ) / 2 ≤ 1 - a := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg b]
  have hdist : secondCollisionDistanceSq s = (a - 1) ^ 2 + b ^ 2 := by
    dsimp [secondCollisionDistanceSq, a, b, leviCivitaPosition]
    ring
  have hdnonneg : 0 ≤ secondCollisionDistanceSq s := by
    rw [hdist]
    positivity
  have hsq : (Real.sqrt (secondCollisionDistanceSq s)) ^ 2 =
      secondCollisionDistanceSq s := Real.sq_sqrt hdnonneg
  have hsqrt : 0 ≤ Real.sqrt (secondCollisionDistanceSq s) := Real.sqrt_nonneg _
  rw [hdist] at hsq hsqrt ⊢
  by_contra h
  have hlt : Real.sqrt ((a - 1) ^ 2 + b ^ 2) < (1 - ρ) / 2 :=
    lt_of_not_ge h
  have hδpos : 0 < (1 - ρ) / 2 := by linarith
  have hprod : 0 <
      ((1 - a) - Real.sqrt ((a - 1) ^ 2 + b ^ 2)) *
        ((1 - a) + Real.sqrt ((a - 1) ^ 2 + b ^ 2)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [sq_nonneg b]
