-- Prove2me | solution 1 for BookProof.Starobinsky.confV_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:43:17.629034+00:00
-- url     : https://prove2.me/submissions/1feeaa9f-ce67-4b7e-bf6d-ccac805aaf40

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.confV_ge
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
import Theorems.Thm_BookProof_Starobinsky_confV_completed_square
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
open BookProof.Starobinsky












open Filter Topology


open BookProof.FarisLavine BookProof.NavierStokesFlow
open BookProof.QuantumGravityDensitized BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) (Rc : ℝ) :
    -(M ^ 4 / (16 * alpha)) ≤ confV M alpha Rc := by

  rw [confV_completed_square halpha.ne' Rc]
  have : 0 ≤ alpha * (Rc - M ^ 2 / (4 * alpha)) ^ 2 := mul_nonneg halpha.le (sq_nonneg _)
  linarith
