-- Prove2me | solution 1 for BookProof.ScalaronDensitized.physConf_esa
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:06:34.660983+00:00
-- url     : https://prove2.me/submissions/1ad7f5b8-6638-45d7-8c17-eacd4e7a0402
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.physConf_esa
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_ScalaronDensitized_physConf_hasZeroDeficiencyOn_transfer
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesFlow
open BookProof.ScalaronDensitized




open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution :
    EssentiallySelfAdjointOn (physConfCore M alpha)
      ((physConfCore M alpha).subtype.comp (physConfOp M alpha)) :=
  (essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn _ _).2
      (physConf_hasZeroDeficiencyOn_transfer M alpha)
