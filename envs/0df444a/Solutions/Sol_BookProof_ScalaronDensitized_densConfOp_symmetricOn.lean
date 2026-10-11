-- Prove2me | solution 1 for BookProof.ScalaronDensitized.densConfOp_symmetricOn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:05:51.432623+00:00
-- url     : https://prove2.me/submissions/40f131d6-a1c1-49bb-a1ac-9f2caaee32b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.densConfOp_symmetricOn
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_NavierStokesFlow_FockContinuum_multOp_isSymmetricDom
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQuantumGravityHalfDensity
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
    SymmetricOn (densConfCore M alpha)
      ((densConfCore M alpha).subtype.comp (densConfOp M alpha)) := multOp_isSymmetricDom qgSrcMeasure (measurable_densConfV M alpha)
