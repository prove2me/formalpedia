-- Prove2me | solution 1 for FairSelling.price_mem_breakpoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:18.799931+00:00
-- url     : https://prove2.me/submissions/a2c92564-5c01-488b-8e3b-9523bd6eb405

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TPSCompute

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) (g : G) : p g ∈ breakpoints v p := by
  classical
  simp only [breakpoints, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr ⟨g, Finset.mem_univ g, rfl⟩)
end FairSelling
