-- Prove2me | solution 1 for FairChores.cbar_le_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:58.327132+00:00
-- url     : https://prove2.me/submissions/3a27ea2f-3a14-42dd-89f1-930ca6f6ba77

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
theorem _root_.solution (t : T) : cbar c p t ≤ c t := min_le_left _ _
end FairChores
