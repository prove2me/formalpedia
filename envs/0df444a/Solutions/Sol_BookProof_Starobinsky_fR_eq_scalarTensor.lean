-- Prove2me | solution 1 for BookProof.Starobinsky.fR_eq_scalarTensor
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:11:02.75556+00:00
-- url     : https://prove2.me/submissions/b4c1c64f-d527-45f0-9cde-c123e998a8d5

-- Generated from ChapterStarobinskyPotential.lean — solution of BookProof.Starobinsky.fR_eq_scalarTensor
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
theorem solution {M alpha : ℝ} (hM : M ≠ 0) (halpha : alpha ≠ 0) (R : ℝ) :
    fR M alpha R
      = M ^ 2 / 2 * scalaron M alpha R * R - Upot M alpha (scalaron M alpha R) := by

  have hM2 : M ^ 2 ≠ 0 := pow_ne_zero 2 hM
  simp only [fR, scalaron, Upot]
  field_simp
  ring
