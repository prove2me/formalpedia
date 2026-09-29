-- Prove2me | solution 1 for BookProof.Starobinsky.starobinskyV_tendsto_plateau
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:08.186981+00:00
-- url     : https://prove2.me/submissions/0a65b675-0fed-4031-9bb4-3b35679e6316

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.starobinskyV_tendsto_plateau
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
theorem solution {M alpha : ℝ} (hM : 0 < M) :
    Tendsto (fun phi => starobinskyV M alpha phi) atTop (𝓝 (M ^ 4 / (16 * alpha))) := by

  have hc : 0 < Real.sqrt (2 / 3) / M := div_pos (Real.sqrt_pos.mpr (by norm_num)) hM
  have hlin : Tendsto (fun phi : ℝ => -(Real.sqrt (2 / 3)) * phi / M) atTop atBot := by
    have h : Tendsto (fun phi : ℝ => -(Real.sqrt (2 / 3) / M) * phi) atTop atBot :=
      Filter.Tendsto.const_mul_atTop_of_neg (by linarith : -(Real.sqrt (2 / 3) / M) < 0)
        tendsto_id
    refine h.congr fun phi => ?_
    field_simp
  have hexp : Tendsto (fun phi : ℝ => Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) atTop
      (𝓝 0) := Real.tendsto_exp_atBot.comp hlin
  have h2 := ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub hexp).pow 2
  simpa [starobinskyV] using h2.const_mul (M ^ 4 / (16 * alpha))
