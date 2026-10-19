-- Prove2me | solution 1 for BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T02:17:53.925149+00:00
-- url     : https://prove2.me/submissions/691b4e12-0e76-4ce2-93cd-2e47db024386

-- Generated from ChapterCyclicDirectSum.lean — solution of BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace
import Mathlib
import Definitions.Def_ChapterCyclicDirectSum
import Theorems.Thm_BookProof_ChapterCyclicDirectSum_starProjection_eq_of_hasSum
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
theorem solution {S : Set H} (hS : OrthogonalCyclicFamily T hT S)
    (htop : (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure = ⊤) (v : H) :
    HasSum (fun x : S => (cyclicSubspace T hT (x : H)).starProjection v) v := by

  have hsum := isHilbertSum_cyclicSubspace T hT hS htop
  have hortho := orthogonalFamily_cyclicSubspace T hT hS
  set w := hsum.linearIsometryEquiv v with hw
  have hv : hsum.linearIsometryEquiv.symm w = v := by
    rw [hw, LinearIsometryEquiv.symm_apply_apply]
  have hHas : HasSum (fun x : S => ((w x : H))) v := by
    have := hsum.hasSum_linearIsometryEquiv_symm w
    rwa [hv] at this
  have hmem : ∀ x : S, ((w x : H)) ∈ cyclicSubspace T hT (x : H) := fun x => (w x).2
  have := starProjection_eq_of_hasSum (V := fun x : S => cyclicSubspace T hT (x : H))
    hortho hmem hHas
  simpa only [this] using hHas
