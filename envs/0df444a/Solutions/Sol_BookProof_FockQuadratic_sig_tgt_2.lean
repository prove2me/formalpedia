-- Prove2me | solution 2 for BookProof.FockQuadratic.sig_tgt
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:12:46.675194+00:00
-- url     : https://prove2.me/submissions/88109a29-57de-4754-9dc6-782488627830

-- Generated from ChapterFockQuadraticEsa.lean — theorem BookProof.FockQuadratic.sig_tgt
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

theorem solution {ω : ι → ℝ} {P Q a : Idx ι} (h : P ≤ a) :
    sig ω (tgt P Q a) = sig ω a - wsum ω P - deg P + wsum ω Q + deg Q := by
  have hadd (u v : Idx ι) : wsum ω (u + v) = wsum ω u + wsum ω v := by
    simp [wsum, Finsupp.sum_add_index', Nat.cast_add, mul_add]
  have hw : wsum ω (a - P) + wsum ω P = wsum ω a := by
    rw [← hadd, tsub_add_cancel_of_le' h]
  have hd : (deg (a - P) : ℝ) + deg P = deg a := by
    exact_mod_cast deg_tsub_of_le h
  simp only [sig, tgt, hadd, deg_add, Nat.cast_add]
  linarith

#print axioms solution
