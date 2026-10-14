-- Prove2me | solution 1 for BookProof.ScalaronFock.fockSmoothPotential_esa
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:12.311837+00:00
-- url     : https://prove2.me/submissions/7b5469a9-d7d6-4846-b47d-617d3710d784

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.fockSmoothPotential_esa
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_essentiallySelfAdjointOn
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
theorem solution (W : ∀ n, E n → ℝ)
    (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) :
    EssentiallySelfAdjointOn (nestedCore E) (fockSmoothPotentialOp W hW) := dsOp_essentiallySelfAdjointOn _ (fun n => smoothPotential_essentiallySelfAdjoint (W n) (hW n))
