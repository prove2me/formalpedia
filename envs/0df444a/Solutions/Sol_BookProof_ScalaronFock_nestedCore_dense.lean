-- Prove2me | solution 1 for BookProof.ScalaronFock.nestedCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:08:03.798287+00:00
-- url     : https://prove2.me/submissions/22da3247-7416-4838-865c-de36376a17e7

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.nestedCore_dense
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_DirectSumEsa_dsCore_dense
import Theorems.Thm_BookProof_ScalaronEsa_ccDomain_dense
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
theorem solution :
    Dense ((nestedCore E : Submodule ℂ (nestedFock E)) : Set (nestedFock E)) := dsCore_dense (fun _ => ccDomain_dense)
