-- Prove2me | solution 1 for BirkhoffGlobalSection.left_negative_closure_nonpositive_energy
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T18:10:16.667558+00:00
-- url     : https://prove2.me/submissions/a535fa11-1ac7-4314-bc70-3b5254f9b47c

import Mathlib
import Theorems.Thm_BirkhoffGlobalSection_left_negative_closure_avoids_second_collision

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∀ s ∈ closure
      (connectedComponentIn
        {t : Phase | leviCivitaHamiltonian μ c t < 0 ∧
          0 < secondCollisionDistanceSq t}
        (fun _ : Fin 4 => (0 : ℝ))),
      leviCivitaHamiltonian μ c s ≤ 0 := by
  let N : Set Phase :=
    {s | leviCivitaHamiltonian μ c s < 0 ∧
      0 < secondCollisionDistanceSq s}
  let C : Set Phase := closure
    (connectedComponentIn N (fun _ : Fin 4 => (0 : ℝ)))
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
  have hclosed : IsClosed (C ∩ (leviCivitaHamiltonian μ c) ⁻¹' Set.Iic 0) :=
    hK.preimage_isClosed_of_isClosed isClosed_closure isClosed_Iic
  have hsubset : connectedComponentIn N (fun _ : Fin 4 => (0 : ℝ)) ⊆
      C ∩ (leviCivitaHamiltonian μ c) ⁻¹' Set.Iic 0 := by
    intro s hs
    exact ⟨subset_closure hs,
      le_of_lt ((connectedComponentIn_subset N (fun _ => 0) hs).1)⟩
  intro s hs
  exact (closure_minimal hsubset hclosed hs).2
