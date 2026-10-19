-- Prove2me | solution 1 for BookProof.ChapterA.cplxify_commutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:46:25.211138+00:00
-- url     : https://prove2.me/submissions/ac4c6c6a-2e63-4e9f-ad31-4c83cf815f11

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.cplxify_commutes
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {T : V →L[ℝ] V}
    (hT : ∀ x, T (Complex.I • x) = Complex.I • T x) (hTc : RealCommutes M T) :
    M.Commutes (cplxify T hT) := by

  intro m hm
  ext x
  simp only [ContinuousLinearMap.mul_apply, cplxify_apply]
  exact hTc m hm x
