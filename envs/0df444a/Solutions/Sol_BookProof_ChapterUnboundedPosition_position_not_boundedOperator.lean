-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.position_not_boundedOperator
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-31T01:27:03.247479+00:00
-- url     : https://prove2.me/submissions/e054cd62-aa1c-423e-bfa7-73942332e1fd

-- Generated from ChapterUnboundedPosition.lean — solution of BookProof.ChapterUnboundedPosition.position_not_boundedOperator
import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Theorems.Thm_BookProof_ChapterUnboundedPosition_position_unbounded
open BookProof.ChapterUnboundedPosition



open scoped ENNReal InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite (L2Z)

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ T : L2Z →L[ℂ] L2Z, ∀ psi : mulDomain positionField,
      mulOp positionField psi = T (psi : L2Z) := by
    rintro ⟨T, hT⟩
    refine position_unbounded ⟨‖T‖, fun psi => ?_⟩
    rw [hT psi]
    exact T.le_opNorm _

