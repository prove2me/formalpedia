-- Prove2me | solution 1 for BirkhoffGlobalSection.regularized_ray_energy_continuous_on_segment
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T10:26:31.706229+00:00
-- url     : https://prove2.me/submissions/2829ef9b-d5eb-491b-86ab-337db936021d

import Mathlib
import Definitions.Def_BirkhoffGlobalSection

open BirkhoffGlobalSection

theorem solution (μ c : ℝ) (x : Phase) (R : ℝ)
    (hfree : ∀ r : ℝ, 0 ≤ r → r ≤ R →
      0 < secondCollisionDistanceSq (fun i : Fin 4 => r * x i)) :
    ContinuousOn (fun r : ℝ => leviCivitaHamiltonian μ c
      (fun i : Fin 4 => r * x i)) (Set.Icc 0 R) := by
  let s : ℝ → Phase := fun r i => r * x i
  let P : ℝ → ℝ := fun r =>
    wNormSq (s r) / 2 + c * zNormSq (s r) - (1 - μ) / 2 +
      2 * zNormSq (s r) * ((s r) 0 * (s r) 3 - (s r) 1 * (s r) 2) -
      μ * ((s r) 0 * (s r) 3 + (s r) 1 * (s r) 2)
  have hP : Continuous P := by
    dsimp [P, s, wNormSq, zNormSq]
    fun_prop
  have hN : Continuous (fun r => μ * zNormSq (s r)) := by
    dsimp [s, zNormSq]
    fun_prop
  have hD : Continuous (fun r =>
      Real.sqrt (secondCollisionDistanceSq (s r))) := by
    dsimp [s, secondCollisionDistanceSq]
    fun_prop
  have hDne : ∀ r ∈ Set.Icc (0 : ℝ) R,
      Real.sqrt (secondCollisionDistanceSq (s r)) ≠ 0 := by
    intro r hr
    exact ne_of_gt (Real.sqrt_pos.2 (hfree r hr.1 hr.2))
  change ContinuousOn (fun r => P r -
    μ * zNormSq (s r) / Real.sqrt (secondCollisionDistanceSq (s r)))
      (Set.Icc 0 R)
  exact hP.continuousOn.sub (hN.continuousOn.div hD.continuousOn hDne)
