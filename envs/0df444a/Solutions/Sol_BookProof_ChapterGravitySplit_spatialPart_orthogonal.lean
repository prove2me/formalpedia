-- Prove2me | solution 1 for BookProof.ChapterGravitySplit.spatialPart_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:31:55.343882+00:00
-- url     : https://prove2.me/submissions/7703ccf9-c551-4e4c-b9a4-50e1f427694f

-- Generated from ChapterGravitySplit.lean — solution of BookProof.ChapterGravitySplit.spatialPart_orthogonal
import Mathlib
import Definitions.Def_ChapterGravitySplit
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravitySplit




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (v x : Fin 4 → ℝ) (hv : minkSq v = -1) :
    minkForm (spatialPart v x) v = 0 := by

  unfold minkForm;
  unfold spatialPart; simp only [mulVec, dotProduct] ; ring;
  unfold spatialProj; simp [ * ] ; ring;
  unfold minkSq at hv; simp_all [ Fin.sum_univ_four, lower ] ; ring;
  grobner
