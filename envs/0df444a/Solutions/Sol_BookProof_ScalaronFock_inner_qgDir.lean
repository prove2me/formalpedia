-- Prove2me | solution 1 for BookProof.ScalaronFock.inner_qgDir
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:13.201933+00:00
-- url     : https://prove2.me/submissions/36bd840b-f72a-429d-bd63-c2ca247ea0f6

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.inner_qgDir
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ScalaronFock



open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (x : qgSector n) (j : Fin n) (i : Fin 2) :
    (inner ℝ x (qgDir n j i) : ℝ) = x (j, i) := by

  rw [qgDir, EuclideanSpace.inner_single_right]
  simp
