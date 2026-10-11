-- Prove2me | solution 1 for BookProof.VielbeinFock.shearEnergy_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:45.090739+00:00
-- url     : https://prove2.me/submissions/5d2bfca0-6ecd-46e4-9830-52cfbc859a8e

-- Generated from ChapterVielbeinFiberFock.lean — solution of BookProof.VielbeinFock.shearEnergy_apply
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Theorems.Thm_BookProof_VielbeinFock_inner_vielbeinDir
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
    (x : vielbeinSector d n) :
    shearEnergy d om n j x = ∑ i : Fin d, om i ^ 2 / 2 * (x (j, i.castSucc)) ^ 2 := by

  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_vielbeinDir]
