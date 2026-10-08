-- Prove2me | solution 1 for BookProof.ChapterA4h.prop87_assembled
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:51:05.056349+00:00
-- url     : https://prove2.me/submissions/0092b324-2dfd-4a1e-881c-f54d6fd2e32e

import Mathlib
import Definitions.Def_ChapterA4h
open Matrix BookProof.ChapterA3 BookProof.ChapterA4e BookProof.ChapterA4f BookProof.ChapterA5 BookProof.ChapterA4h
set_option maxHeartbeats 0
variable (R : Type*)

theorem solution (Mk : MackeyImprimitivity R)
    (Wg : WignerClassification R Mk) (ρ : R) :
    PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.massive ∨
    PoincareType.of (Mk.massSq ρ) (Mk.contSpin ρ) = PoincareType.masslessDiscrete := by
  have hnn : 0 ≤ Mk.massSq ρ := by
    unfold MackeyImprimitivity.massSq
    positivity
  unfold PoincareType.of
  rcases lt_or_eq_of_le hnn with h | h
  · left; simp [h]
  · right
    rw [← h]
    simp [Wg.no_continuous_spin ρ h.symm]

#print axioms solution

