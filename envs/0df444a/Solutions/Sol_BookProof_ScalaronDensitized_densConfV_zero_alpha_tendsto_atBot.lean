-- Prove2me | solution 1 for BookProof.ScalaronDensitized.densConfV_zero_alpha_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:05:33.708451+00:00
-- url     : https://prove2.me/submissions/cb151f1d-c9c8-4f15-8ec2-a178f0c8089e

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.densConfV_zero_alpha_tendsto_atBot
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {M : ℝ} (hM : M ≠ 0) :
    Tendsto (fun y => densConfV M 0 y) atTop atBot := by

  have hpos : 0 < M ^ 2 / 2 := by positivity
  have hsq : Tendsto (fun y : ℝ => y ^ 2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have h : Tendsto (fun t : ℝ => -(M ^ 2 / 2) * t) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -(M ^ 2 / 2) < 0) tendsto_id
  refine (h.comp hsq).congr fun y => ?_
  simp [densConfV, confV, Function.comp]
