-- Prove2me | solution 1 for FairSelling.exists_max_outcome
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:18.227801+00:00
-- url     : https://prove2.me/submissions/106510f5-5777-4602-926d-6a40942ab292

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Theorems.Thm_FairSelling_minUtil_outcomeOf
import Theorems.Thm_FairSelling_outcomeOf_valid
import Theorems.Thm_FairSelling_exists_opt_money
import Theorems.Thm_FairSelling_exists_assignform_ge
import Theorems.Thm_FairSelling_outcomeOf_cover

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) (hn : 0 < n) :
    ∃ o : Outcome G n, o.Valid p ∧
      (o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ) ∧
      ∀ o' : Outcome G n, o'.Valid p → minUtil v o' ≤ minUtil v o := by
  choose m hm using fun assign => exists_opt_money v p hp assign
  obtain ⟨a0, ha0⟩ := Finite.exists_max
    (fun assign : G → Option (Fin n) => minUtilData v assign (m assign))
  refine ⟨outcomeOf a0 (m a0), outcomeOf_valid p a0 (m a0) (hm a0).1 (hm a0).2.1,
    outcomeOf_cover a0 (m a0), ?_⟩
  intro o' ho'
  obtain ⟨assign', m', hm0', hms', hle'⟩ := exists_assignform_ge hn v p hv o' ho'
  calc minUtil v o' ≤ minUtilData v assign' m' := hle'
    _ ≤ minUtilData v assign' (m assign') := (hm assign').2.2 m' hm0' hms'
    _ ≤ minUtilData v a0 (m a0) := ha0 assign'
    _ = minUtil v (outcomeOf a0 (m a0)) := (minUtil_outcomeOf v a0 (m a0)).symm
end FairSelling
