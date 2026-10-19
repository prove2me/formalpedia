-- Prove2me | solution 1 for BookProof.ChapterCyclicDecomposition.invariant_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:51:26.773738+00:00
-- url     : https://prove2.me/submissions/7f8cac4d-651b-4105-94d6-c113d0404f84

-- Generated from ChapterCyclicDecomposition.lean — solution of BookProof.ChapterCyclicDecomposition.invariant_orthogonal
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
import Definitions.Def_ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

set_option maxHeartbeats 1000000 in
theorem solution {M : Submodule ℂ H} (hM : Invariant T hT M) :
    Invariant T hT Mᗮ := by

  intro g v hv
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hadj : (ContinuousLinearMap.adjoint (cfcHom hT g)) u = cfcHom hT (star g) u := by
    have h : star (cfcHom hT g) = cfcHom hT (star g) := (map_star (cfcHom hT) g).symm
    rw [← ContinuousLinearMap.star_eq_adjoint, h]
  have h0 : (inner ℂ (cfcHom hT (star g) u) v : ℂ) = 0 :=
    (Submodule.mem_orthogonal M v).1 hv _ (hM (star g) u hu)
  rw [← ContinuousLinearMap.adjoint_inner_left, hadj, h0]
