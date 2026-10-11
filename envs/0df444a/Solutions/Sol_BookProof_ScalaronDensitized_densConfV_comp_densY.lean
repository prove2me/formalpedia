-- Prove2me | solution 1 for BookProof.ScalaronDensitized.densConfV_comp_densY
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:03:57.168529+00:00
-- url     : https://prove2.me/submissions/799ef728-c0fe-4630-b66e-85dda0dd2864

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.densConfV_comp_densY
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_ScalaronDensitized_densConfV_apply
import Theorems.Thm_BookProof_QuantumGravityDensitized_densY_sq
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {M alpha e : ℝ} (he : 0 ≤ e) :
    densConfV M alpha (densY e) = confV M alpha e := by

  rw [densConfV_apply, densY_sq he]
