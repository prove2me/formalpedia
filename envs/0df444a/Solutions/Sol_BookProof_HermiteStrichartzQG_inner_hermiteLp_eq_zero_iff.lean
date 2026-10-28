-- Prove2me | solution 1 for BookProof.HermiteStrichartzQG.inner_hermiteLp_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T05:52:19.196992+00:00
-- url     : https://prove2.me/submissions/2bf30b84-cf87-41a1-a37d-cbafd2fce591

import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Theorems.Thm_BookProof_HermiteCore_hermiteBasis_apply
import Definitions.Def_ChapterStrichartzHermiteQG
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteFunctions
open BookProof.FarisLavine
open BookProof.HermiteCore
open BookProof.HermiteStrichartzQG



open MeasureTheory BookProof.HermiteCore BookProof.FarisLavine
open BookProof.QuantumGravityDensitized

theorem solution {w : L2R} :
    (∀ n : ℕ, (inner ℂ (hermiteLp n) w : ℂ) = 0) ↔ w = 0 := by
  constructor
  · intro h
    have hr : BookProof.HermiteCore.hermiteBasis.repr w = 0 := by
      ext n
      rw [HilbertBasis.repr_apply_apply, BookProof.HermiteCore.hermiteBasis_apply, h n]
      rfl
    simpa using hr
  · rintro rfl n
    exact inner_zero_right _
