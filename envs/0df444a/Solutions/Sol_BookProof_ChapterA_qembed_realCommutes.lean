-- Prove2me | solution 1 for BookProof.ChapterA.qembed_realCommutes
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:08:45.882503+00:00
-- url     : https://prove2.me/submissions/8f865c7f-cb6d-4c92-bb37-974387b90ddb

-- Generated from ChapterA2c.lean — solution of BookProof.ChapterA.qembed_realCommutes
import Mathlib
import Definitions.Def_ChapterA2c
import Theorems.Thm_BookProof_ChapterA_realCommutes_add
import Theorems.Thm_BookProof_ChapterA_realCommutes_mul
import Theorems.Thm_BookProof_ChapterA_realCommutes_smul
import Theorems.Thm_BookProof_ChapterA_realCommutes_algebraMap
import Theorems.Thm_BookProof_ChapterA_realCommutes_mulI
import Theorems.Thm_BookProof_ChapterA_realCommutes_thetaR
import Theorems.Thm_BookProof_ChapterA_qembed_apply
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA



open scoped ComplexConjugate InnerProductSpace Quaternion


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

set_option maxHeartbeats 1000000 in
theorem solution {M : System ℂ V} {θ : AntiUnitary V} (hθ : ∀ x, θ (θ x) = -x)
    (hθc : CommutesAntiUnitary M θ) (q : Quaternion ℝ) :
    RealCommutes M (qembed θ hθ q) := by

  rw [qembed_apply]
  have hi : RealCommutes M (mulI : V →L[ℝ] V) := realCommutes_mulI M
  have hj : RealCommutes M (thetaR θ) := realCommutes_thetaR hθc
  have hk : RealCommutes M (mulI * thetaR θ) := realCommutes_mul hi hj
  exact realCommutes_add
    (realCommutes_add
      (realCommutes_add (realCommutes_algebraMap M q.re) (realCommutes_smul hi q.imI))
      (realCommutes_smul hj q.imJ))
    (realCommutes_smul hk q.imK)
