-- Prove2me | solution 2 for BookProof.NavierStokesFlow.SignedShift.listH_relative_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T21:19:48.399864+00:00
-- url     : https://prove2.me/submissions/5e8d9043-2dc0-4cae-98f1-bbb2cc0f334a

-- Generated from ChapterNavierStokesSignedShift.lean — solution of BookProof.NavierStokesFlow.SignedShift.listH_relative_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesSignedShift
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_SignedHop_hopH_relative_bound
import Theorems.Thm_BookProof_NavierStokesFlow_SignedShift_listH_cons
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.SignedShift










open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}



variable {sym : ι → ℝ} (S : SignedHop ι sym)


































variable {sym : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (L : List (SignedHop ι sym)) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ x : maxDom sym,
      ‖(listH L x : L2I ι)‖ ^ 2
        ≤ a * ‖(diagMax sym x : L2I ι)‖ ^ 2 + b * ‖(x : L2I ι)‖ ^ 2 := by

  induction L with
  | nil =>
      refine ⟨0, 0, le_rfl, le_rfl, fun x => ?_⟩
      simp [listH]
  | cons S L ih =>
      obtain ⟨a, b, ha, hb, hbound⟩ := ih
      refine ⟨2 * (1 / 2) + 2 * a, 2 * (8 * S.K ^ 2) + 2 * b, by linarith,
        by nlinarith [sq_nonneg S.K], fun x => ?_⟩
      have h₁ := SignedHop.hopH_relative_bound S x
      have h₂ := hbound x
      have htri : ‖(listH (S :: L) x : L2I ι)‖
          ≤ ‖(SignedHop.hopH S x : L2I ι)‖ + ‖(listH L x : L2I ι)‖ := by
        simp only [listH_cons, LinearMap.add_apply]
        exact norm_add_le _ _
      have hsq : ‖(listH (S :: L) x : L2I ι)‖ ^ 2
          ≤ 2 * ‖(SignedHop.hopH S x : L2I ι)‖ ^ 2 + 2 * ‖(listH L x : L2I ι)‖ ^ 2 := by
        nlinarith [norm_nonneg (listH (S :: L) x : L2I ι),
          norm_nonneg (SignedHop.hopH S x : L2I ι), norm_nonneg (listH L x : L2I ι),
          sq_nonneg (‖(SignedHop.hopH S x : L2I ι)‖ - ‖(listH L x : L2I ι)‖)]
      nlinarith [h₁, h₂, hsq]
