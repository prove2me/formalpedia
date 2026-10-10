-- Prove2me | solution 1 for BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:22:47.32514+00:00
-- url     : https://prove2.me/submissions/75a143f7-8135-41ce-8245-413706814053

-- Generated from ChapterGravityInvMetric.lean — solution of BookProof.ChapterGravityInvMetric.invSpatialMetric_mulVec_lower_self
import Mathlib
import Definitions.Def_ChapterGravityInvMetric
import Theorems.Thm_BookProof_ChapterGravityProjector_spatialProj_mulVec_self
import Definitions.Def_ChapterGravityMetric
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityInvMetric




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityMetric

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 4 → ℝ) (hv : minkSq v = -1) :
    (invSpatialMetric v).mulVec (lower v) = 0 := by

      convert spatialProj_mulVec_self v hv using 1;
      unfold invSpatialMetric spatialProj;        ext; simp only [mulVec, dotProduct,
                                                         Matrix.add_apply, of_apply,
                                                         Fin.sum_univ_four,
                                                         Fin.isValue] ;
      unfold lower metric; simp only [Fin.isValue, mulVec, dotProduct, Fin.sum_univ_four,
                             diagonal_apply_eq, ↓reduceIte, neg_mul,
                             one_mul, ne_eq, zero_ne_one,
                             not_false_eq_true, diagonal_apply_ne,
                             zero_mul, add_zero, Fin.reduceEq,
                             mul_neg, one_ne_zero, zero_add] ; ring;
      rename_i i; fin_cases i <;> simp [ Matrix.one_apply ]; all_goals ring
