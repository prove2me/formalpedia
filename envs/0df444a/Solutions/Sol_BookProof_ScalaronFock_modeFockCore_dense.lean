-- Prove2me | solution 1 for BookProof.ScalaronFock.modeFockCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:22.874412+00:00
-- url     : https://prove2.me/submissions/a06ebe5d-824f-4c9e-af15-edf98374c778

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.modeFockCore_dense
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Theorems.Thm_BookProof_Starobinsky_mulSymbolDomain_dense
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQuantumGravityDensitized
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
theorem solution :
    Dense ((modeFockCore a b M alpha Rc phi : Submodule ℂ modeFock) : Set modeFock) := dsCore_dense (fun _ => mulSymbolDomain_dense _)
