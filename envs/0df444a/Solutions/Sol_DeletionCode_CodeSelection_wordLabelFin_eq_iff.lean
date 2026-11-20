-- Prove2me | solution 1 for DeletionCode.CodeSelection.wordLabelFin_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:42:16.914713+00:00
-- url     : https://prove2.me/submissions/c09dea5d-695e-4b53-a60b-498f7d682b02

import Definitions.Def_DeletionCode_BipartiteSelection
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_CodeSelection
import Theorems.Thm_DeletionCode_CircleHash_label_range


set_option autoImplicit true
open DeletionCode DeletionCode.CodeSelection
open HeaderRecovery ConflictGraphWitness BipartiteSelection
variable {n k : ℕ}
namespace DeletionCode.CodeSelection
theorem _root_.solution (Q : ℕ) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (x y : Bits n) :
    wordLabelFin Q hQ H x = wordLabelFin Q hQ H y ↔ wordLabel Q H x = wordLabel Q H y := by
  constructor
  · intro h
    have heq : (wordLabel Q H x).toNat = (wordLabel Q H y).toNat := congrArg Fin.val h
    have hx := (CircleHash.label_range Q hQ (H (spectrum k x))).1
    have hy := (CircleHash.label_range Q hQ (H (spectrum k y))).1
    change 0 ≤ wordLabel Q H x at hx
    change 0 ≤ wordLabel Q H y at hy
    omega
  · intro h
    apply Fin.ext
    exact congrArg Int.toNat h
end DeletionCode.CodeSelection
