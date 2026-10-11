-- Prove2me | solution 1 for BookProof.ScalaronFock.qgManyPotential_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:14.154348+00:00
-- url     : https://prove2.me/submissions/66ecbbb3-c796-429f-9be4-d0edc08aa714

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.qgManyPotential_apply
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_ScalaronFock_inner_qgDir
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterScalaronCoreEsa
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.ScalaronFock



open Filter Topology MeasureTheory SchwartzMap


open BookProof.FarisLavine BookProof.Starobinsky BookProof.ScalaronEsa
open BookProof.DirectSumEsa BookProof.StoneBridge BookProof.EsaClosure
open BookProof.QuantumGravityDensitized BookProof.ChapterStoneResolvent

noncomputable section

variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

set_option maxHeartbeats 1000000 in
theorem solution (M alpha : ℝ) (n : ℕ) (x : qgSector n) :
    qgManyPotential M alpha n x
      = ∑ j : Fin n, (confV M alpha (x (j, 0)) + starobinskyV M alpha (x (j, 1))) := by

  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [scalaronFullPotential, inner_qgDir, inner_qgDir]
