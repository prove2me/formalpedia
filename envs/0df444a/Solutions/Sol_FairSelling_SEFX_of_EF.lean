-- Prove2me | solution 1 for FairSelling.SEFX_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:34.808523+00:00
-- url     : https://prove2.me/submissions/5ccb878c-fa96-45e2-9a8f-9c81daaea475

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (h : EF v p o) : SEFX v p o := fun i j =>
  ⟨fun _ => h i j, fun hj => Or.inl (by have := h i j; rw [hj] at this; linarith)⟩
end FairSelling
