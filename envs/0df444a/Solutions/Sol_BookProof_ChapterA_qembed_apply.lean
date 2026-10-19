-- Prove2me | solution 1 for BookProof.ChapterA.qembed_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T00:46:10.089002+00:00
-- url     : https://prove2.me/submissions/d5a766e6-7efc-4fb2-8c63-24bcbc69dbda

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.qembed_apply
import Mathlib
import Definitions.Def_ChapterA2c
import Definitions.Def_ChapterA1
import Definitions.Def_ChapterA
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (θ : AntiUnitary V) (hθ : ∀ x, θ (θ x) = -x) (q : Quaternion ℝ) :
    qembed θ hθ q
      = algebraMap ℝ (V →L[ℝ] V) q.re + q.imI • mulI + q.imJ • thetaR θ
        + q.imK • (mulI * thetaR θ) := rfl
