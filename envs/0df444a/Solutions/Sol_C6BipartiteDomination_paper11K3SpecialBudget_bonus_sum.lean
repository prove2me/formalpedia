-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3SpecialBudget_bonus_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:36.759671+00:00
-- url     : https://prove2.me/submissions/a974b2b2-6685-4699-88dd-9abe4d58df62

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) :
    (∑ u ∈ paper11K3RightVertices G D hCan hmax,
      if u ∈ paper11K3SpecialBudgetVertices G D hCan hmax then (7 : ℤ)
      else 0) =
      7 * ((paper11K3SpecialBudgetVertices G D hCan hmax).card : ℤ) := by
  classical
  let R := paper11K3RightVertices G D hCan hmax
  let P := paper11K3SpecialBudgetVertices G D hCan hmax
  have hfilter : R.filter (fun u => u ∈ P) = P := by
    ext u
    simp [P, paper11K3SpecialBudgetVertices, R]
  calc
    (∑ u ∈ R, if u ∈ P then (7 : ℤ) else 0) =
        ∑ u ∈ R.filter (fun u => u ∈ P), (7 : ℤ) := by
          rw [Finset.sum_filter]
    _ = ∑ u ∈ P, (7 : ℤ) := by rw [hfilter]
    _ = 7 * (P.card : ℤ) := by simp <;> ring
end C6BipartiteDomination
