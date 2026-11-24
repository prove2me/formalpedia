-- Prove2me | solution 1 for FairSelling.SEF1_of_EF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:29.812686+00:00
-- url     : https://prove2.me/submissions/0ffcbcf0-d490-4561-a41f-8b091c91b22d

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
variable {v : Fin n → G → ℝ} {p : G → ℝ} {o : Outcome G n}
namespace FairSelling
theorem _root_.solution (h : EF v p o) : SEF1 v p o := fun i j =>
  ⟨fun _ => h i j, fun hj => Or.inl (by have := h i j; rw [hj] at this; linarith)⟩
end FairSelling
