-- Prove2me | solution 1 for DeletionCode.ClosedWalk.signed_independent_closed_walk_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:09.230676+00:00
-- url     : https://prove2.me/submissions/919a1d20-8749-4d34-a385-13a87c06cb88

import Definitions.Def_DeletionCode_WitnessAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Definitions.Def_DeletionCode_ClosedWalk
import Theorems.Thm_DeletionCode_ClosedWalk_sum_displacements
import Theorems.Thm_DeletionCode_WitnessAlgebra_signed_sum_even


set_option autoImplicit true
open DeletionCode DeletionCode.ClosedWalk
open scoped BigOperators
namespace DeletionCode.ClosedWalk
theorem _root_.solution {I V : Type*} [Fintype I]
    [AddCommGroup V] [Module ℚ V] {m : ℕ}
    (G : I → V) (hG : LinearIndependent ℚ G) (p : Fin (m + 1) → V)
    (label : Fin m → I) (hclosed : p 0 = p (Fin.last m))
    (hsteps : ∀ i : Fin m,
      p i.succ - p i.castSucc = G (label i) ∨
      p i.succ - p i.castSucc = -G (label i)) : Even m := by
  classical
  let positive : Fin m → Prop := fun i => p i.succ - p i.castSucc = G (label i)
  have hstep : ∀ i : Fin m,
      (if positive i then (1 : ℚ) else -1) • G (label i) =
        p i.succ - p i.castSucc := by
    intro i
    by_cases hi : positive i
    · simpa only [if_pos hi, one_smul] using hi.symm
    · have hneg := (hsteps i).resolve_left hi
      simpa only [if_neg hi, neg_smul, one_smul] using hneg.symm
  have hsum : (∑ i : Fin m,
      (if positive i then (1 : ℚ) else -1) • G (label i)) = 0 := by
    simp_rw [hstep]
    rw [sum_displacements, ← hclosed, sub_self]
  simpa using WitnessAlgebra.signed_sum_even G hG label positive hsum
end DeletionCode.ClosedWalk
