-- Prove2me | solution 1 for BookProof.ScalaronFock.qgManyPotential_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:18:16.40293+00:00
-- url     : https://prove2.me/submissions/9ca52932-ae80-4fd1-b89f-8897492013b2

-- Generated from ChapterScalaronFockEsa.lean — solution of BookProof.ScalaronFock.qgManyPotential_ge
import Mathlib
import Definitions.Def_ChapterScalaronFockEsa
import Theorems.Thm_BookProof_ScalaronEsa_scalaronFullPotential_ge
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
theorem solution {M alpha : ℝ} (halpha : 0 < alpha) (n : ℕ) (x : qgSector n) :
    -(n * (M ^ 4 / (16 * alpha))) ≤ qgManyPotential M alpha n x := by

  have hterm : ∀ j : Fin n,
      -(M ^ 4 / (16 * alpha)) ≤ scalaronFullPotential M alpha (qgDir n j 0) (qgDir n j 1) x :=
    fun j => scalaronFullPotential_ge halpha _ _ x
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hterm j)
  simpa [qgManyPotential, Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum
