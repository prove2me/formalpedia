-- Prove2me | solution 1 for DeletionCode.ClosedWalk.sum_displacements
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:15:49.636202+00:00
-- url     : https://prove2.me/submissions/467d5203-b660-4d57-88e4-df9ba905a928

import Definitions.Def_DeletionCode_WitnessAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Definitions.Def_DeletionCode_ClosedWalk

set_option autoImplicit true
open DeletionCode DeletionCode.ClosedWalk
open scoped BigOperators
namespace DeletionCode.ClosedWalk
theorem _root_.solution {V : Type*} [AddCommGroup V] {m : ℕ}
    (p : Fin (m + 1) → V) :
    (∑ i : Fin m, (p i.succ - p i.castSucc)) = p (Fin.last m) - p 0 := by
  rw [Finset.sum_sub_distrib]
  have h := (Fin.sum_univ_succ p).symm.trans (Fin.sum_univ_castSucc p)
  calc
    (∑ i : Fin m, p i.succ) - ∑ i : Fin m, p i.castSucc =
        (p 0 + ∑ i : Fin m, p i.succ) - (p 0 + ∑ i : Fin m, p i.castSucc) := by
      abel
    _ = ((∑ i : Fin m, p i.castSucc) + p (Fin.last m)) -
        (p 0 + ∑ i : Fin m, p i.castSucc) := by rw [h]
    _ = p (Fin.last m) - p 0 := by
      abel
end DeletionCode.ClosedWalk
