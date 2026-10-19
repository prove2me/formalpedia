-- Prove2me | solution 1 for BookProof.ScalaronFock.qgScalaronFock_stone_flow
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:46:48.939745+00:00
-- url     : https://prove2.me/submissions/08d2dac3-035b-45b0-b647-7d50be30a135

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneResolvent
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_esa
import Theorems.Thm_BookProof_ScalaronFock_qgFockCore_dense
import Theorems.Thm_BookProof_ScalaronFock_qgScalaronFock_symmetric
import Theorems.Thm_BookProof_ScalaronFock_qgScalaronFock_esa
-- Generated from ChapterScalaronFockEsa.lean — theorem BookProof.ScalaronFock.qgScalaronFock_stone_flow
open BookProof.EsaClosure
open BookProof.StoneBridge
open BookProof.ScalaronFock


open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]


theorem solution (M alpha : ℝ) :
    ∃ (T : UnboundedSelfAdjoint qgFock) (U : ℝ → (qgFock →L[ℂ] qgFock)),
      IsSelfAdjointExtension (qgScalaronFockHamiltonian M alpha) T.op ∧ IsStoneFlow T U := by
  exact BookProof.StoneBridge.exists_stone_flow_of_esa _ BookProof.ScalaronFock.qgFockCore_dense
    (BookProof.ScalaronFock.qgScalaronFock_symmetric M alpha) (BookProof.ScalaronFock.qgScalaronFock_esa M alpha)

