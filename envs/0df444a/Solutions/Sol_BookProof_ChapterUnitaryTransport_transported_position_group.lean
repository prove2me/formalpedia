-- Prove2me | solution 1 for BookProof.ChapterUnitaryTransport.transported_position_group
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:39:27.878833+00:00
-- url     : https://prove2.me/submissions/c263efd6-c7fc-41e9-afa7-1a4c2dedb801

import Mathlib
import Definitions.Def_ChapterUnitaryTransport
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterUnboundedPosition
-- Generated from ChapterUnitaryTransport.lean — theorem BookProof.ChapterUnitaryTransport.transported_position_group
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterUnitaryTransport


open scoped InnerProductSpace


variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]


theorem solution (f : ℤ → ℝ) (W : L2Z ≃ₗᵢ[ℂ] K) (s t : ℝ) (y : K) :
    transportUnitary W (phaseUnitary f (s + t)) y
      = transportUnitary W (phaseUnitary f s) (transportUnitary W (phaseUnitary f t) y) := by
  simp only [transportUnitary, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply]
  congr 1
  refine lp.ext (funext fun k => ?_)
  change BookProof.ChapterUnboundedPosition.phase f (s + t) k * _ =
    BookProof.ChapterUnboundedPosition.phase f s k * (BookProof.ChapterUnboundedPosition.phase f t k * _)
  rw [← mul_assoc]
  congr 1
  simp only [BookProof.ChapterUnboundedPosition.phase, ← Complex.exp_add]
  congr 1
  push_cast; ring

