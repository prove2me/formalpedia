-- Prove2me | solution 1 for BookProof.ChapterEulerNState.tailProd_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:51:14.812426+00:00
-- url     : https://prove2.me/submissions/92282353-939f-455e-8460-834c09cc8b38

-- Generated from ChapterEulerNState.lean — solution of BookProof.ChapterEulerNState.tailProd_nonneg
import Mathlib
import Definitions.Def_ChapterEulerNState
open BookProof.ChapterEulerNState



open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (m : ℕ) : 0 ≤ tailProd θ m := Finset.prod_nonneg fun _ _ => sq_nonneg _
