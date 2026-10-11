-- Prove2me | solution 1 for BookProof.VielbeinFock.vielbeinManyPotential_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:49.212862+00:00
-- url     : https://prove2.me/submissions/4e08c755-f73e-47ac-a9af-4a2079c74871

-- Generated from ChapterVielbeinFiberFock.lean — solution of BookProof.VielbeinFock.vielbeinManyPotential_nonneg
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Theorems.Thm_BookProof_VielbeinFock_shearEnergy_nonneg
import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
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
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) (d : ℕ)
    (om : Fin d → ℝ) (n : ℕ) (x : vielbeinSector d n) :
    0 ≤ vielbeinManyPotential M alpha d om n x := by

  refine Finset.sum_nonneg (fun j _ => ?_)
  have h1 := shearEnergy_nonneg d om n j x
  have h2 := starobinskyV_nonneg (M := M) halpha
    (inner ℝ x (vielbeinDir d n j (Fin.last d)) : ℝ)
  linarith
