-- Prove2me | solution 1 for BookProof.ScalaronFock.fockSmoothPotential_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:08:04.828144+00:00
-- url     : https://prove2.me/submissions/8d40f5e7-3ca1-498f-abb6-64ea596bb604

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.fockSmoothPotential_symmetric
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_symmetricOn
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_symmetric
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
    SymmetricOn (nestedCore E) (fockSmoothPotentialOp W hW) := dsOp_symmetricOn _ (fun n => smoothPotential_symmetric (W n) (hW n))
