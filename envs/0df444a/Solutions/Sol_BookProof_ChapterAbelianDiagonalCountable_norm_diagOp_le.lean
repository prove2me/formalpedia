-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.norm_diagOp_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:35:58.025881+00:00
-- url     : https://prove2.me/submissions/a4e756c3-734a-46b2-8a7a-58531e294183

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.norm_diagOp_le
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (d : EllInf) : ‖diagOp d‖ ≤ ‖d‖ := LinearMap.mkContinuous_norm_le _ (norm_nonneg _) _
