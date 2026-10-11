-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.oddSchwartz_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:06.479771+00:00
-- url     : https://prove2.me/submissions/cf193918-4975-4065-b344-41abce6e4b94

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.oddSchwartz_apply
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) : oddSchwartz x = oddBump x := rfl
