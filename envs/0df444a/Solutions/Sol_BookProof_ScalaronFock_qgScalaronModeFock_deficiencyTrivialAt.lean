-- Prove2me | solution 1 for BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T17:17:21.952882+00:00
-- url     : https://prove2.me/submissions/e10c5004-4bee-4350-a847-8f88ae0a9039

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.qgScalaronModeFock_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_deficiencyTrivialAt
import Theorems.Thm_BookProof_ScalaronEsa_qgScalaronMode_deficiencyTrivialAt
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
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
variable (a b : ℕ → ℕ → ℝ) (M alpha : ℝ) (Rc phi : ℕ → ℕ → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (modeFockCore a b M alpha Rc phi)
      (qgScalaronModeFockHamiltonian a b M alpha Rc phi) z :=
  dsOp_deficiencyTrivialAt _
      (fun n => qgScalaronMode_deficiencyTrivialAt (a n) (b n) M alpha (Rc n) (phi n) hz)
