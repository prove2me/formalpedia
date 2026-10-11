-- Prove2me | solution 1 for BookProof.VielbeinFock.shearEnergy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:48.091257+00:00
-- url     : https://prove2.me/submissions/6e4e5727-5230-441d-9fe9-3b34f25426d8

-- Generated from ChapterVielbeinFiberFock.lean — solution of BookProof.VielbeinFock.shearEnergy_nonneg
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
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
theorem solution (d : ℕ) (om : Fin d → ℝ) (n : ℕ) (j : Fin n)
    (x : vielbeinSector d n) : 0 ≤ shearEnergy d om n j x := Finset.sum_nonneg (fun i _ => by positivity)
