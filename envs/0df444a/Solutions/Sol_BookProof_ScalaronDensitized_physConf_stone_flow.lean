-- Prove2me | solution 1 for BookProof.ScalaronDensitized.physConf_stone_flow
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:07:48.826828+00:00
-- url     : https://prove2.me/submissions/6bbbeb32-df7c-421d-9348-136bd58d27ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.physConf_stone_flow
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_ScalaronDensitized_physConfCore_dense
import Theorems.Thm_BookProof_ScalaronDensitized_physConfOp_symmetricOn
import Theorems.Thm_BookProof_ScalaronDensitized_physConf_esa
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
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
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 physMeasure))
      (U : ℝ → (Lp ℂ 2 physMeasure →L[ℂ] Lp ℂ 2 physMeasure)),
      IsSelfAdjointExtension
        ((physConfCore M alpha).subtype.comp (physConfOp M alpha)) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ (physConfCore_dense M alpha) (physConfOp_symmetricOn M alpha)
      (physConf_esa M alpha)
