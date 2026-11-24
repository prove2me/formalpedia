-- Prove2me | solution 1 for FairChores.MMSset_bddBelow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:17:35.527091+00:00
-- url     : https://prove2.me/submissions/61417025-9e4a-423c-b096-f839dc4c007d

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cost_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hn : 0 < n) : BddBelow (MMSset n c p) := by
  refine ⟨0, ?_⟩
  rintro r ⟨o, hvalid, hle⟩
  exact le_trans (cost_nonneg hc hvalid ⟨0, hn⟩) (hle ⟨0, hn⟩)
end FairChores
