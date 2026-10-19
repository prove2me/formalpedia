-- Prove2me | solution 1 for BookProof.ChapterA.cembed_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:46:08.897975+00:00
-- url     : https://prove2.me/submissions/8367d686-28b9-40b2-86d7-afa29eca6e49

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.cembed_injective
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution [Nontrivial V] :
    Function.Injective (cembed : ℂ → (V →L[ℝ] V)) := (cembed : ℂ →ₐ[ℝ] (V →L[ℝ] V)).toRingHom.injective
