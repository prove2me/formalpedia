-- Prove2me | solution 1 for BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:08:05.815729+00:00
-- url     : https://prove2.me/submissions/f8e309b2-87ce-4865-ae04-4fe1462638c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.fockSmoothPotential_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_deficiencyTrivialAt
import Theorems.Thm_BookProof_ScalaronEsa_smoothPotential_deficiencyTrivial
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
    (hW : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (W n)) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (nestedCore E) (fockSmoothPotentialOp W hW) z := dsOp_deficiencyTrivialAt _ (fun n => smoothPotential_deficiencyTrivial (W n) (hW n) hz)
