-- Prove2me | solution 1 for BookProof.ChapterDoubleSlit.slit_open_state
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:25:06.146289+00:00
-- url     : https://prove2.me/submissions/d2904e92-98af-4a47-93db-c47dcc9f2529

-- Generated from ChapterDoubleSlit.lean — solution of BookProof.ChapterDoubleSlit.slit_open_state
import Mathlib
import Definitions.Def_ChapterDoubleSlit
import Theorems.Thm_BookProof_ChapterDoubleSlit_H_involutive
open BookProof.ChapterDoubleSlit



open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution : H *ᵥ (H *ᵥ psi0) = psi0 := by

  rw [Matrix.mulVec_mulVec, H_involutive, Matrix.one_mulVec]
