-- Prove2me | solution 1 for BookProof.ScalaronFock.qgManyPotential_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:17.368894+00:00
-- url     : https://prove2.me/submissions/32e101fa-79f9-4e39-bf51-6499e9b802ef

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.qgManyPotential_esa
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterScalaronCoreEsa
open BookProof.ScalaronFock



open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (n : ℕ) :
    EssentiallySelfAdjointOn (ccDomain (qgSector n))
      (opCc (qgManyPotential M alpha n) (contDiff_qgManyPotential M alpha n)) := smoothPotential_essentiallySelfAdjoint _ _
