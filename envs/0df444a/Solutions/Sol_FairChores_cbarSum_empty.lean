-- Prove2me | solution 1 for FairChores.cbarSum_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:10:09.449637+00:00
-- url     : https://prove2.me/submissions/1b76daa9-413c-41af-b2f0-17ec7e24607d

import Mathlib
import Definitions.Def_RequestProject_ChoresModel

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) : cbarSum c p (∅ : Finset T) = 0 := by
  simp [cbarSum]
end FairChores
