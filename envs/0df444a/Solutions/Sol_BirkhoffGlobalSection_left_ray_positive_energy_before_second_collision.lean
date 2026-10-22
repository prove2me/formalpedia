-- Prove2me | solution 1 for BirkhoffGlobalSection.left_ray_positive_energy_before_second_collision
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:21:24.467373+00:00
-- url     : https://prove2.me/submissions/7658dde6-f7e3-4733-bde7-314c452a25d9

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_subcritical_circle_energy_positive
import Theorems.Thm_BirkhoffGlobalSection_nonvertical_ray_reaches_inner_circle

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ x ∈ unitThreeSphere,
      ∃ R : ℝ, 0 < R ∧
        leviCivitaHamiltonian μ c (fun i : Fin 4 => R * x i) > 0 ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ R →
          0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i) := by
  obtain ⟨r, hr, hr1, hcircle⟩ :=
    inner_lagrange_subcritical_circle_energy_positive μ c hμ0 hμ1 hc
  intro x hx
  by_cases hz : 0 < zNormSq x
  · obtain ⟨R, hR, hq, hfree⟩ :=
      nonvertical_ray_reaches_inner_circle r hr hr1 x hz
    refine ⟨R, hR, ?_, hfree⟩
    apply hcircle
    dsimp [leviCivitaPosition] at hq ⊢
    nlinarith [hq]
  · have hznonneg : 0 ≤ zNormSq x := by dsimp [zNormSq]; positivity
    have hz0 : zNormSq x = 0 := le_antisymm (le_of_not_gt hz) hznonneg
    have hx0 : x 0 = 0 := by
      dsimp [zNormSq] at hz0
      nlinarith [sq_nonneg (x 1)]
    have hx1 : x 1 = 0 := by
      dsimp [zNormSq] at hz0
      nlinarith [sq_nonneg (x 0)]
    have hw : (x 2) ^ 2 + (x 3) ^ 2 = 1 := by
      have hunit : zNormSq x + wNormSq x = 1 := hx
      dsimp [zNormSq, wNormSq] at hunit
      nlinarith [hz0]
    refine ⟨2, by norm_num, ?_, ?_⟩
    · dsimp [leviCivitaHamiltonian, wNormSq, zNormSq,
        secondCollisionDistanceSq]
      simp [hx0, hx1] <;> nlinarith [hw, hμ1]
    · intro t ht0 ht2
      dsimp [secondCollisionDistanceSq]
      simp [hx0, hx1]
