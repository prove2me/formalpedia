-- Prove2me | solution 1 for BookProof.QgCouplingDGammaSum.creVec_add
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:21:55.206984+00:00
-- url     : https://prove2.me/submissions/199941e3-1784-42f1-8d3c-e90cbcdb7701

-- Generated from ChapterQgCouplingDGammaSum.lean — solution of BookProof.QgCouplingDGammaSum.creVec_add
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Theorems.Thm_BookProof_QgCouplingDGammaSum_creVec_eq_sum
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.QgCouplingDGammaSum




open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (v w : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (v + w) x = creVec v x + creVec w x := by

  classical
  set L : Finset ℕ := (v + w).support ∪ (v.support ∪ w.support) with hL
  have h1 : (v + w).support ⊆ L := Finset.subset_union_left
  have h2 : v.support ⊆ L := fun j hj =>
    Finset.mem_union_right _ (Finset.mem_union_left _ hj)
  have h3 : w.support ⊆ L := fun j hj =>
    Finset.mem_union_right _ (Finset.mem_union_right _ hj)
  rw [creVec_eq_sum h1, creVec_eq_sum h2, creVec_eq_sum h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.add_apply, add_smul]
