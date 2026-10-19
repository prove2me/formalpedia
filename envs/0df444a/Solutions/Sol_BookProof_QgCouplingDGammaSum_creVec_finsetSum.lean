-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.creVec_finsetSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:44:26.885385+00:00
-- url     : https://prove2.me/submissions/8521c685-5887-499d-b687-b57b1107e0fe

import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFockSecondQuantization
import Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_add
import Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_zero
-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.creVec_finsetSum
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}


theorem solution (s : Finset ι) (f : ι → (ℕ →₀ ℂ)) (x : FockAlg) :
    creVec (∑ i ∈ s, f i) x = ∑ i ∈ s, creVec (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [BookProof.QgCouplingDGammaSum.creVec_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, BookProof.QgCouplingDGammaSum.creVec_add, ih]

