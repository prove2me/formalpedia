-- Prove2me | solution 1 for BookProof.Starobinsky.confV_zero_alpha_tendsto_atBot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:01.778487+00:00
-- url     : https://prove2.me/submissions/9aef315e-464e-48aa-b088-bdfa2300ec20

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.confV_zero_alpha_tendsto_atBot
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
theorem solution {M : ℝ} (hM : M ≠ 0) :
    Tendsto (fun Rc => confV M 0 Rc) atTop atBot := by

  have hpos : 0 < M ^ 2 / 2 := by positivity
  have h : Tendsto (fun Rc : ℝ => -(M ^ 2 / 2) * Rc) atTop atBot :=
    Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -(M ^ 2 / 2) < 0) tendsto_id
  refine h.congr fun Rc => ?_
  simp [confV]
