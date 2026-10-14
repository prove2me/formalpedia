-- Prove2me | solution 1 for BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T19:25:22.249873+00:00
-- url     : https://prove2.me/submissions/929d3190-e8fd-413c-a6d1-15c7a4e4d4c6

-- Generated from ChapterDirectSumEsa.lean — solution of BookProof.DirectSumEsa.dsOp_deficiencyTrivialAt
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
import Theorems.Thm_BookProof_DirectSumEsa_dsOp_single
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.DirectSumEsa



open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution (H : ∀ i, D i →ₗ[ℂ] G i) {z : ℂ}
    (h : ∀ i, DeficiencyTrivialAt (D i) (H i) z) :
    DeficiencyTrivialAt (dsCore D) (dsOp H) z := by

  classical
  intro w hw
  have hcoord : ∀ i, ((w : lp G 2) : ∀ i, G i) i = 0 := by
    intro i
    refine h i _ (fun u => ?_)
    have hv := hw ⟨lp.single 2 i ((u : G i)), single_mem_dsCore i u⟩
    rw [dsOp_single H i u] at hv
    rw [lp.inner_single_left, lp.inner_single_left] at hv
    exact hv
  refine lp.ext (funext fun i => ?_)
  rw [hcoord i]
  simp
