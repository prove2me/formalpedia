-- Prove2me | solution 1 for BookProof.ScalaronDensitized.densConf_stone_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:07:47.776804+00:00
-- url     : https://prove2.me/submissions/8ada7073-2d00-456e-8af5-891beea4387d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.densConf_stone_flow
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_ScalaronDensitized_densConfCore_dense
import Theorems.Thm_BookProof_ScalaronDensitized_densConfOp_symmetricOn
import Theorems.Thm_BookProof_ScalaronDensitized_densConf_esa
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)
variable {X : Type*} [MeasurableSpace X]

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 qgSrcMeasure))
      (U : ℝ → (Lp ℂ 2 qgSrcMeasure →L[ℂ] Lp ℂ 2 qgSrcMeasure)),
      IsSelfAdjointExtension
        ((densConfCore M alpha).subtype.comp (densConfOp M alpha)) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ (densConfCore_dense M alpha) (densConfOp_symmetricOn M alpha)
      (densConf_esa M alpha)
