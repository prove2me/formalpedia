-- Prove2me | solution 1 for Chou.isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isSolvable
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-21T14:46:35.454789+00:00
-- url     : https://prove2.me/submissions/731ddc8b-c426-46aa-b6cd-c24fd0affcba

import Theorems.Thm_Rosenblatt_isPolycyclic_of_fg_of_isSolvable_of_not_hasFreeSubsemigroupOfRankTwo
import Theorems.Thm_Rosenblatt_isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic
import Mathlib

/-!
# Chou's Rosenblatt citation, reduced to Rosenblatt's own two theorems

Chou, *Elementary amenable groups*, Illinois J. Math. 24 (1980), p. 401, settles the solvable
case of Theorem 3.2′ by citing Rosenblatt: "If `G` is a finitely generated solvable group then
`G` is either almost nilpotent or it contains a free subsemigroup on two generators."

That sentence is the composite of two results in Rosenblatt's §4, and this file is the
composition, nothing more:

* **Theorem 4.7** (p. 41), proved: a finitely generated solvable group with no free subsemigroup
  of rank two is polycyclic.
* **Theorem 4.12** (p. 44), open: a polycyclic group is almost nilpotent or contains a free
  subsemigroup of rank two.

Given a finitely generated solvable `G`, split on whether `G` has a free subsemigroup of rank
two. If it does, the right disjunct is immediate. If it does not, Theorem 4.7 makes `G`
polycyclic, Theorem 4.12 offers the dichotomy, and the right disjunct is excluded by the very
assumption of this branch, leaving "almost nilpotent".

The case split is what lets the inclusive form of Theorem 4.12 do the work of Rosenblatt's
exclusive "but not both": the exclusivity is never needed, because the branch in which the
disjunct has to be discarded is the branch that assumed its negation.
-/

namespace Rosenblatt

/-- Chou's citation of Rosenblatt (p. 401), as the composite of Rosenblatt's Theorems 4.7 and
4.12. -/
theorem isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isSolvable {G : Type*} [Group G]
    [Group.FG G] [Group.IsSolvable G] :
    Group.IsVirtuallyNilpotent G ∨ Chou.HasFreeSubsemigroupOfRankTwo G := by
  by_cases hfree : Chou.HasFreeSubsemigroupOfRankTwo G
  · exact Or.inr hfree
  · exact Or.inl
      ((isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isPolycyclic
        (isPolycyclic_of_fg_of_isSolvable_of_not_hasFreeSubsemigroupOfRankTwo hfree)).resolve_right
        hfree)

end Rosenblatt

theorem solution {G : Type*} [Group G]
    [Group.FG G] [Group.IsSolvable G] :
    Group.IsVirtuallyNilpotent G ∨ Chou.HasFreeSubsemigroupOfRankTwo G :=
  Rosenblatt.isVirtuallyNilpotent_or_hasFreeSubsemigroupOfRankTwo_of_isSolvable
