-- Prove2me | solution 1 for BookProof.Starobinsky.starobinskyV_tendsto_atBot_atTop
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:07.350982+00:00
-- url     : https://prove2.me/submissions/53638afd-f0ee-41fc-bb80-3c4d5226ffdb

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.starobinskyV_tendsto_atBot_atTop
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
theorem solution {M alpha : ℝ} (hM : 0 < M) (halpha : 0 < alpha) :
    Tendsto (fun phi => starobinskyV M alpha phi) atBot atTop := by

  have hcpos : 0 < Real.sqrt (2 / 3) / M := div_pos (Real.sqrt_pos.mpr (by norm_num)) hM
  have hlin : Tendsto (fun phi : ℝ => -(Real.sqrt (2 / 3)) * phi / M) atBot atTop := by
    have h : Tendsto (fun phi : ℝ => -(Real.sqrt (2 / 3) / M) * phi) atBot atTop :=
      Filter.Tendsto.const_mul_atBot_of_neg (by linarith : -(Real.sqrt (2 / 3) / M) < 0)
        tendsto_id
    refine h.congr fun phi => ?_
    field_simp
  have hexp : Tendsto (fun phi : ℝ => Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) atBot
      atTop := Real.tendsto_exp_atTop.comp hlin
  have hsub : Tendsto (fun phi : ℝ => Real.exp (-(Real.sqrt (2 / 3)) * phi / M) - 1) atBot
      atTop := Filter.tendsto_atTop_add_const_right _ (-1) hexp |>.congr fun phi => by ring
  have hsq : Tendsto
      (fun phi : ℝ => (1 - Real.exp (-(Real.sqrt (2 / 3)) * phi / M)) ^ 2) atBot atTop := by
    refine (hsub.atTop_mul_atTop₀ hsub).congr fun phi => ?_
    ring
  have hconst : 0 < M ^ 4 / (16 * alpha) := div_pos (by positivity) (by linarith)
  simpa [starobinskyV] using hsq.const_mul_atTop hconst
