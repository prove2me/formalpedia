-- Prove2me | solution 1 for BookProof.VielbeinFock.vielbeinFock_potential_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:55.438302+00:00
-- url     : https://prove2.me/submissions/23be2045-ba96-4326-a490-0454f959a9b5

-- Generated from ChapterVielbeinFiberFock.lean — solution of BookProof.VielbeinFock.vielbeinFock_potential_ge
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Theorems.Thm_BookProof_VielbeinFock_vielbeinManyPotential_nonneg
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
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ) (om : Fin d → ℝ)
    (n : ℕ) (x : vielbeinSector d n) : 0 ≤ vielbeinManyPotential M alpha d om n x := vielbeinManyPotential_nonneg halpha d om n x
