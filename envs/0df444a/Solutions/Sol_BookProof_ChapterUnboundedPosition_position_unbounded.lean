-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.position_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:44:10.025992+00:00
-- url     : https://prove2.me/submissions/0b427daf-32f3-43e5-89b2-e7a55b366a48

import Mathlib
import Theorems.Thm_BookProof_ChapterUnboundedPosition_single_mem_mulDomain
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
-- Generated from ChapterUnboundedPosition.lean — theorem BookProof.ChapterUnboundedPosition.position_unbounded
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition


open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)
theorem solution :
    ¬ ∃ C : ℝ, ∀ psi : mulDomain positionField,
      ‖mulOp positionField psi‖ ≤ C * ‖(psi : L2Z)‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hmem := BookProof.ChapterUnboundedPosition.single_mem_mulDomain positionField (n : ℤ) 1
  have h := hC ⟨_, hmem⟩
  have heq : (BookProof.ChapterUnboundedPosition.mulOp positionField ⟨_, hmem⟩ : L2Z) =
      lp.single 2 (n : ℤ) ((n : ℂ)) := by
    ext k
    simp only [BookProof.ChapterUnboundedPosition.mulOp, LinearMap.coe_mk, AddHom.coe_mk,
      lp.single_apply, positionField]
    by_cases hk : k = (n : ℤ)
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [heq] at h
  simp only [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] at h
  norm_num at h
  linarith
