-- Prove2me | solution 1 for FairChores.cbar_le_price
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:01.405912+00:00
-- url     : https://prove2.me/submissions/3aacb18b-a939-4257-be5c-782e7205ee8f

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
theorem _root_.solution (t : T) : cbar c p t ≤ p t := min_le_right _ _
end FairChores
