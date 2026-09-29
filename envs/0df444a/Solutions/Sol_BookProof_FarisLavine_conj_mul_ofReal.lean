-- Prove2me | solution 1 for BookProof.FarisLavine.conj_mul_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T07:50:11.936124+00:00
-- url     : https://prove2.me/submissions/79188eaf-9299-4e10-8fcf-943d300205d7

-- Generated from ChapterFarisLavine.lean — solution of BookProof.FarisLavine.conj_mul_ofReal
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.FarisLavine





variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (b : ℝ) (z : ℂ) :
    (b : ℂ) * z * (starRingEnd ℂ) z = ((b * Complex.normSq z : ℝ) : ℂ) := by

  rw [show (b : ℂ) * z * (starRingEnd ℂ) z = (b : ℂ) * ((starRingEnd ℂ) z * z) by ring,
    ← Complex.normSq_eq_conj_mul_self]
  push_cast
  ring
