-- Prove2me | solution 1 for BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:47.084635+00:00
-- url     : https://prove2.me/submissions/81a7690c-160b-46e4-a815-cd9e4747a3c4

-- Generated from ChapterVielbeinFiberFock.lean — solution of BookProof.VielbeinFock.vielbeinManyPotential_scalaron_fiber
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Theorems.Thm_BookProof_VielbeinFock_vielbeinManyPotential_apply
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterScalaronFockEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.VielbeinFock



open Filter Topology MeasureTheory


open BookProof.Starobinsky BookProof.ScalaronEsa BookProof.ScalaronFock
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.FarisLavine BookProof.ChapterStoneResolvent

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (om : Fin 0 → ℝ) (n : ℕ)
    (x : vielbeinSector 0 n) :
    vielbeinManyPotential M alpha 0 om n x
      = ∑ j : Fin n, starobinskyV M alpha (x (j, Fin.last 0)) := by

  simp [vielbeinManyPotential_apply]
