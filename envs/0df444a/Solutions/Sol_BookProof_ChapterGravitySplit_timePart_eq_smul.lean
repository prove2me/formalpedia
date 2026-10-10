-- Prove2me | solution 1 for BookProof.ChapterGravitySplit.timePart_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:31:43.87821+00:00
-- url     : https://prove2.me/submissions/312d517a-2e26-469b-9c83-28ad2a136c6f

-- Generated from ChapterGravitySplit.lean — solution of BookProof.ChapterGravitySplit.timePart_eq_smul
import Mathlib
import Definitions.Def_ChapterGravitySplit
import Definitions.Def_ChapterGravityProjector
import Definitions.Def_ChapterGravityTimeProj
open BookProof.ChapterGravitySplit




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector
open BookProof.ChapterGravityTimeProj

set_option maxHeartbeats 1000000 in
theorem solution (v x : Fin 4 → ℝ) :
    timePart v x = (-(minkForm x v)) • v := by

  ext a;
  unfold timePart minkForm; simp only [mulVec, dotProduct, Fin.sum_univ_four, Fin.isValue,
      neg_add_rev, Pi.smul_apply, smul_eq_mul] ; ring;
  unfold timeProj; norm_num; ring;
