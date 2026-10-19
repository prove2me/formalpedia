-- Prove2me | solution 1 for BookProof.ChapterA.realCommutes_thetaR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:45:52.013642+00:00
-- url     : https://prove2.me/submissions/3c97e706-26d3-4699-bd5c-66a0ab08b4c2

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.realCommutes_thetaR
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {θ : AntiUnitary V}
    (hθ : CommutesAntiUnitary M θ) : RealCommutes M (thetaR θ) := by

  intro m hm x
  simp only [thetaR_apply]
  exact hθ m hm x
