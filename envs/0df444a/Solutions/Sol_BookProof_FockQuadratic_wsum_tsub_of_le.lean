-- Prove2me | solution 1 for BookProof.FockQuadratic.wsum_tsub_of_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:12:47.993674+00:00
-- url     : https://prove2.me/submissions/3d60f483-d7a5-4ed5-96e7-8b04f7184519

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.wsum_tsub_of_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterOperatorSeriesEsa
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
import Definitions.Def_ChapterA3n
open BookProof.ChapterA3n
open BookProof.FockQuadratic

variable {ι : Type*}


open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

theorem solution {ω : ι → ℝ} {P a : Idx ι} (h : P ≤ a) :
    wsum ω (a - P) + wsum ω P = wsum ω a := by
  have hadd (u v : Idx ι) : wsum ω (u + v) = wsum ω u + wsum ω v := by
    simp [wsum, Finsupp.sum_add_index', Nat.cast_add, mul_add]
  rw [← hadd, tsub_add_cancel_of_le' h]

#print axioms solution
