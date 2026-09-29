-- Prove2me | solution 1 for BookProof.Starobinsky.starobinskyV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:06.524985+00:00
-- url     : https://prove2.me/submissions/d3c0963b-f675-4b56-8403-8c880dbdeb15

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.starobinskyV_nonneg
import Mathlib
import Definitions.Def_ChapterStarobinskyPotential
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
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) (phi : ℝ) :
    0 ≤ starobinskyV M alpha phi := by

  have h16 : (0 : ℝ) < 16 * alpha := by linarith
  have h1 : 0 ≤ M ^ 4 / (16 * alpha) := div_nonneg (by positivity) h16.le
  exact mul_nonneg h1 (sq_nonneg _)
