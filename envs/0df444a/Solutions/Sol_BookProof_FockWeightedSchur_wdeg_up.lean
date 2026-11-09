-- Prove2me | solution 1 for BookProof.FockWeightedSchur.wdeg_up
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T09:51:10.66682+00:00
-- url     : https://prove2.me/submissions/893b4649-445f-451b-b393-71fd8ddc3a24

-- Generated from ChapterFockWeightedSchurEsa.lean — solution of BookProof.FockWeightedSchur.wdeg_up
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Theorems.Thm_BookProof_FockWeightedSchur_wdeg_eq_sum
import Theorems.Thm_BookProof_FockSchur_up_apply_prime
import Theorems.Thm_BookProof_FockSecondQuantization_support_up
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
theorem solution (j : ℕ) (α : Conf) : wdeg w (up j α) = wdeg w α + w j ^ 2 := by

  classical
  have h1 : (up j α).support ⊆ insert j α.support := support_up j α
  have h2 : α.support ⊆ insert j α.support := Finset.subset_insert _ _
  rw [wdeg_eq_sum h1, wdeg_eq_sum h2]
  have hcongr : ∀ i ∈ insert j α.support,
      w i ^ 2 * (((up j α) i : ℕ) : ℝ)
        = w i ^ 2 * ((α i : ℕ) : ℝ) + (if i = j then w j ^ 2 else 0) := by
    intro i _
    rw [up_apply_prime j α i]
    by_cases h : i = j
    · subst h; push_cast; simp; ring
    · simp [h]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib]
  congr 1
  simp
