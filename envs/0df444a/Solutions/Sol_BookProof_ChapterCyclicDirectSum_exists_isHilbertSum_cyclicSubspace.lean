-- Prove2me | solution 1 for BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:17:48.260985+00:00
-- url     : https://prove2.me/submissions/cdac0f12-9dc0-4785-b505-4e1c9c4d6811

-- Generated from ChapterCyclicDirectSum.lean — solution of BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_exists_cyclic_decomposition
import Definitions.Def_ChapterCyclicDecomposition
open BookProof.ChapterCyclicDirectSum



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterCyclicDecomposition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧
      IsHilbertSum ℂ (fun x : S => (cyclicSubspace T hT (x : H)))
        (fun x : S => (cyclicSubspace T hT (x : H)).subtypeₗᵢ) := by

  obtain ⟨S, hS, htop⟩ := exists_cyclic_decomposition T hT
  exact ⟨S, hS, isHilbertSum_cyclicSubspace T hT hS htop⟩
