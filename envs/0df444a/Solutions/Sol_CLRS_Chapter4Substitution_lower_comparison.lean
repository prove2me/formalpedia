-- Prove2me | solution 1 for CLRS.Chapter4Substitution.lower_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Chutong
-- created : 2026-10-11T06:34:28.658753+00:00
-- url     : https://prove2.me/submissions/b6c81d43-d4d9-478c-b972-8319ae2d7f2d

import Definitions.Def_CLRS_Chapter4_Substitution
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section
namespace CLRS

/-!
CLRS §4.3: substitution as comparison with a proposed upper or lower bound.

Subproblem sizes are natural numbers; costs and tolls are natural-valued.
Every non-base problem has a finite list of strictly smaller children. The
number of children and their sizes may vary with the parent, and children need
not have equal sizes. Thus floor/ceiling splits, unequal splits, missing
branches, and repeated subproblems fit the same interface.

These theorems establish facts about numerical recurrences. Applying them to a
program additionally requires a proof connecting that program's charged cost
to the corresponding recurrence, as in the source-linked algorithm analyses.
-/
namespace Chapter4Substitution





@[simp] theorem childSum_cons (size : Nat) (sizes : List Nat) (cost : Nat → Nat) :
    childSum (size :: sizes) cost = cost size + childSum sizes cost := by
  simp [childSum]

/-- Only comparisons at sizes actually occurring in the list are needed. -/
theorem childSum_mono (sizes : List Nat) (lower upper : Nat → Nat)
    (bound : ∀ size ∈ sizes, lower size ≤ upper size) :
    childSum sizes lower ≤ childSum sizes upper := by
  induction sizes with
  | nil => exact Nat.le_refl 0
  | cons size sizes ih =>
    simp only [childSum_cons]
    exact Nat.add_le_add (bound size (by simp))
      (ih (fun child member => bound child (by simp [member])))







































/-! Natural-valued asymptotic bounds. Constants and thresholds are natural
numbers; constants must be positive, and finitely many sizes below the threshold
are unrestricted. This API does not define real powers or assert a Master theorem. -/































end Chapter4Substitution

end CLRS
end

namespace CLRS
end CLRS
open CLRS
namespace CLRS.Chapter4Substitution
end CLRS.Chapter4Substitution
open CLRS.Chapter4Substitution

theorem solution (children : Nat → List Nat) (toll : Nat → Nat)
    (cutoff : Nat) (cost candidate : Nat → Nat)
    (smaller : SmallerChildren children cutoff)
    (base : ∀ n, n < cutoff → candidate n ≤ cost n)
    (recurrence : LowerRecurrence children toll cutoff cost)
    (substitution : LowerCandidate children toll cutoff candidate) :
    ∀ n, candidate n ≤ cost n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases small : n < cutoff
    · exact base n small
    · have large : cutoff ≤ n := by omega
      have childrenBound : childSum (children n) candidate ≤ childSum (children n) cost :=
        childSum_mono (children n) candidate cost
          (fun child member => ih child (smaller n large child member))
      exact Nat.le_trans (substitution n large)
        (Nat.le_trans (Nat.add_le_add_left childrenBound (toll n)) (recurrence n large))
