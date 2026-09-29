-- Prove2me | solution 1 for CannonFloydParry.getLast_exponents_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-16T21:16:58.265878+00:00
-- url     : https://prove2.me/submissions/7f4dc21e-92d4-4528-ad2a-b042e23635d1

import Definitions.Def_CannonFloydParry_Trees
import Mathlib

namespace CannonFloydParry

/-- The exponent list of a tree is never empty: it has one entry per leaf, and every tree has at
least one leaf. -/
lemma exponents_ne_nil (t : TTree) : t.exponents ≠ [] := by
  induction t with
  | leaf => simp [TTree.exponents]
  | node l r _ ihr =>
      rw [TTree.exponents]
      simpa using fun _ => ihr

end CannonFloydParry

open CannonFloydParry

theorem solution (t : TTree) : t.exponents.getLast? = some 0 := by
  induction t with
  | leaf => rfl
  | node l r _ ihr =>
      rw [TTree.exponents, List.getLast?_append_of_ne_nil _ (exponents_ne_nil r)]
      exact ihr
