-- Prove2me | solution 1 for BookProof.ChapterGravityTimeProj.timeProj_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:32:51.070822+00:00
-- url     : https://prove2.me/submissions/c96ae06d-73ec-47e4-88b7-f2ed9dd1b352

-- Generated from ChapterGravityTimeProj.lean — solution of BookProof.ChapterGravityTimeProj.timeProj_idempotent
import Mathlib
import Definitions.Def_ChapterGravityTimeProj
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityTimeProj




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    timeProj v * timeProj v = timeProj v := by

  unfold timeProj;
  ext a b; simp only [mul_apply, of_apply, mul_neg, neg_mul, neg_neg, Fin.sum_univ_four,
      Fin.isValue] ; ring;
  unfold minkSq at hv; simp_all only [lower, Fin.sum_univ_four, Fin.isValue] ;
  linear_combination' hv * v a * ( metric *ᵥ v ) b
