-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_boundary_closed
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T17:44:22.674694+00:00
-- url     : https://prove2.me/submissions/da49f186-a0dd-423b-8aaa-6e50e99e99c9

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_avoids_second_collision

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    IsClosed
      {s : Phase | s ∈ closure
        (connectedComponentIn
          {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
            0 < secondCollisionDistanceSq t}
          (fun _ : Fin 4 => (0 : ℝ))) ∧
        leviCivitaHamiltonian μ c s = 0 ∧
        0 < secondCollisionDistanceSq s} := by
  let C : Set Phase := closure
    (connectedComponentIn
      {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
        0 < secondCollisionDistanceSq t}
      (fun _ : Fin 4 => (0 : ℝ)))
  have hfree : ∀ s ∈ C, 0 < secondCollisionDistanceSq s :=
    left_negative_closure_avoids_second_collision μ c hμ0 hμ1 hc
  let P : Phase → ℝ := fun s =>
    wNormSq s / 2 + c * zNormSq s - (1 - μ) / 2 +
      2 * zNormSq s * (s 0 * s 3 - s 1 * s 2) -
      μ * (s 0 * s 3 + s 1 * s 2)
  have hP : Continuous P := by
    dsimp [P, wNormSq, zNormSq]
    fun_prop
  have hN : Continuous (fun s : Phase => μ * zNormSq s) := by
    dsimp [zNormSq]
    fun_prop
  have hD : Continuous (fun s : Phase =>
      Real.sqrt (secondCollisionDistanceSq s)) := by
    dsimp [secondCollisionDistanceSq]
    fun_prop
  have hDne : ∀ s ∈ C,
      Real.sqrt (secondCollisionDistanceSq s) ≠ 0 := by
    intro s hs
    exact ne_of_gt (Real.sqrt_pos.2 (hfree s hs))
  have hK : ContinuousOn (leviCivitaHamiltonian μ c) C := by
    change ContinuousOn (fun s => P s -
      μ * zNormSq s / Real.sqrt (secondCollisionDistanceSq s)) C
    exact hP.continuousOn.sub (hN.continuousOn.div hD.continuousOn hDne)
  have hclosed : IsClosed (C ∩ (leviCivitaHamiltonian μ c) ⁻¹' {0}) :=
    hK.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  convert hclosed using 1
  ext s
  constructor
  · intro hs
    exact ⟨hs.1, hs.2.1⟩
  · intro hs
    exact ⟨hs.1, hs.2, hfree s hs.1⟩
