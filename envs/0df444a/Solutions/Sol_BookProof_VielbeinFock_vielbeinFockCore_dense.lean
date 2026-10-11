-- Prove2me | solution 1 for BookProof.VielbeinFock.vielbeinFockCore_dense
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:51.527831+00:00
-- url     : https://prove2.me/submissions/9a12bc52-e3c0-4c50-a2ca-93e8a1c0ec57

-- Generated from ChapterVielbeinFiberFock.lean — solution of BookProof.VielbeinFock.vielbeinFockCore_dense
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Theorems.Thm_BookProof_ScalaronFock_nestedCore_dense
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.VielbeinFock



open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (d : ℕ) :
    Dense ((vielbeinFockCore d : Submodule ℂ (vielbeinFock d)) : Set (vielbeinFock d)) := nestedCore_dense
