-- Prove2me | solution 1 for FairChores.mem_MMSset_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:26:02.047626+00:00
-- url     : https://prove2.me/submissions/020fd192-e23f-4922-b831-09b311e30635

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Definitions.Def_RequestProject_ChoresMMSPartition
import Theorems.Thm_FairChores_maxCost_le_iff

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T] {n : ℕ}
namespace FairChores
theorem _root_.solution (hn : 0 < n) (c p : T → ℝ) (r : ℝ) :
    r ∈ MMSset n c p ↔ ∃ o : Outcome T n, o.Valid p ∧ maxCost c o ≤ r := by
  constructor
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (maxCost_le_iff hn c o r).mpr h⟩
  · rintro ⟨o, hv, h⟩; exact ⟨o, hv, (maxCost_le_iff hn c o r).mp h⟩
end FairChores
