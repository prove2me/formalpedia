-- Prove2me | solution 1 for BookProof.FockWeightedSchur.inner_wgt_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:52:35.683995+00:00
-- url     : https://prove2.me/submissions/1fe3c4cc-9f96-4ab1-b6db-1894c5cafff9

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.inner_wgt_symm
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wgt_apply
import Theorems.Thm_BookProof_FockWeightedSchur_support_wgt_subset
import Theorems.Thm_BookProof_FockSecondQuantization_inner_toLp_of_subset
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockWeightedSchur




open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.FockSecondQuantization

noncomputable section

variable {w : ℕ → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (u v : FockAlg) :
    (inner ℂ (toLp (wgt w u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (wgt w v)) := by

  classical
  have hsu : (wgt w u).support ⊆ u.support ∪ v.support :=
    (support_wgt_subset u).trans Finset.subset_union_left
  have hsv : u.support ⊆ u.support ∪ v.support := Finset.subset_union_left
  rw [inner_toLp_of_subset hsu v, inner_toLp_of_subset hsv (wgt w v)]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [wgt_apply, wgt_apply, map_mul, Complex.conj_ofReal]
  ring
