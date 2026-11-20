-- Prove2me | solution 1 for DeletionCode.ClosedWalk.not_odd_signed_independent_closed_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:22.990179+00:00
-- url     : https://prove2.me/submissions/9813ba65-8898-4757-a90d-2e3819b2cd06

import Definitions.Def_DeletionCode_WitnessAlgebra
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Definitions.Def_DeletionCode_ClosedWalk
import Theorems.Thm_DeletionCode_ClosedWalk_signed_independent_closed_walk_even

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
      p i.succ - p i.castSucc = -G (label i)) : ¬ Odd m := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb⟩ := signed_independent_closed_walk_even G hG p label hclosed hsteps
  omega
end DeletionCode.ClosedWalk
