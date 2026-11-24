-- Prove2me | solution 1 for FairSelling.vval_mem_breakpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:52:15.640421+00:00
-- url     : https://prove2.me/submissions/60c3cccf-06fe-4233-aa92-2476e16c1622

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (g : G) : v g ∈ breakpoints v p := by
  classical
  simp only [breakpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inl ⟨g, Finset.mem_univ g, rfl⟩)
end FairSelling
