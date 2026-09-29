-- Prove2me | solution 1 for BalancedAlgebra.composable_leftUnit_rightIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T15:44:36.2801+00:00
-- url     : https://prove2.me/submissions/6c38cb99-5ee6-4817-930d-8852ff98eb04

import Mathlib
import Definitions.Def_BalancedAlgebra_core

set_option linter.unusedSectionVars false

namespace BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra

/-- In a balanced algebra the elements composable with a fixed left unit form a right ideal. -/
theorem composable_leftUnit_rightIdeal {A : Type*} (P : PartialAlgebra A) (hP : P.Balanced)
    (u : A) (hu : P.IsLeftUnit u) : P.RightIdeal {b : A | P.IsDefined u b} := by
  intro a b c ha hop
  obtain ⟨x, hx⟩ := ha
  rw [hu a x hx] at hx
  have hl : IsDef (P.lprod u a b) := ⟨c, by rw [lprod_eq_some]; exact ⟨a, hx, hop⟩⟩
  have hr := (hP u a b).1 hl
  rwa [show P.rprod u a b = P.op u c from by simp [rprod, hop]] at hr

end BAFix

open BalancedAlgebra BalancedAlgebra.PartialAlgebra in
theorem solution {A : Type*} (P : PartialAlgebra A) (hP : P.Balanced)
    (u : A) (hu : P.IsLeftUnit u) : P.RightIdeal {b : A | P.IsDefined u b} :=
  BAFix.composable_leftUnit_rightIdeal P hP u hu
