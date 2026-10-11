-- Prove2me | solution 1 for BookProof.ScalaronFock.qgManyPotential_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:15.28016+00:00
-- url     : https://prove2.me/submissions/08d69c20-899c-4c22-97e7-47f0861f7272

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.qgManyPotential_one
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
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
theorem solution (M alpha : ℝ) (x : qgSector 1) :
    qgManyPotential M alpha 1 x
      = scalaronFullPotential M alpha (qgDir 1 0 0) (qgDir 1 0 1) x := by

  simp [qgManyPotential]
