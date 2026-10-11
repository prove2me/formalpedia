-- Prove2me | solution 1 for BookProof.ChapterSphericalPlancherel.oddSchwartz_odd
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:29:08.169998+00:00
-- url     : https://prove2.me/submissions/142ae790-0fef-4b03-8700-2571de562b66

-- Generated from ChapterSphericalPlancherel.lean — solution of BookProof.ChapterSphericalPlancherel.oddSchwartz_odd
import Mathlib
import Definitions.Def_ChapterSphericalPlancherel
import Theorems.Thm_BookProof_ChapterSphericalPlancherel_oddBump_odd
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalPlancherel




open MeasureTheory Set Real SchwartzMap
open scoped FourierTransform ContDiff
open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (x : ℝ) : oddSchwartz (-x) = -oddSchwartz x := oddBump_odd x
