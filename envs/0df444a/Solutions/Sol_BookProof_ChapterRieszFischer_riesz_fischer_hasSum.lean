-- Prove2me | solution 1 for BookProof.ChapterRieszFischer.riesz_fischer_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:52:27.30559+00:00
-- url     : https://prove2.me/submissions/0bb08d95-c619-4e41-aefc-3e21f36ad4c7

-- Generated from ChapterRieszFischer.lean — solution of BookProof.ChapterRieszFischer.riesz_fischer_hasSum
import Mathlib
import Definitions.Def_ChapterRieszFischer
open BookProof.ChapterRieszFischer



open Filter
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (f : Ell2) :
    HasSum (fun i => lp.single 2 i ((f : ℕ → ℝ) i)) f := lp.hasSum_single (by simp) f
