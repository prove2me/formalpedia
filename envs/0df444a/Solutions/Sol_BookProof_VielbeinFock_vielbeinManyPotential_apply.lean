-- Prove2me | solution 1 for BookProof.VielbeinFock.vielbeinManyPotential_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:25:46.074294+00:00
-- url     : https://prove2.me/submissions/95c2be4c-d9ce-4c8c-8346-8286022836d3

-- Generated from ChapterVielbeinFiberFock.lean — solution of BookProof.VielbeinFock.vielbeinManyPotential_apply
import Mathlib
import Definitions.Def_ChapterVielbeinFiberFock
import Theorems.Thm_BookProof_VielbeinFock_inner_vielbeinDir
import Theorems.Thm_BookProof_VielbeinFock_shearEnergy_apply
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
theorem solution (M alpha : ℝ) (d : ℕ) (om : Fin d → ℝ) (n : ℕ)
    (x : vielbeinSector d n) :
    vielbeinManyPotential M alpha d om n x
      = ∑ j : Fin n, ((∑ i : Fin d, om i ^ 2 / 2 * (x (j, i.castSucc)) ^ 2)
        + starobinskyV M alpha (x (j, Fin.last d))) := by

  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [shearEnergy_apply, inner_vielbeinDir]
