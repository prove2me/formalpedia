-- Prove2me | solution 1 for FairChores.cbar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:09.782827+00:00
-- url     : https://prove2.me/submissions/74069c7f-08b5-4f73-83db-e565bf8b2e93

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
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (t : T) : 0 ≤ cbar c p t :=
  le_min (hc t) (hp t)
end FairChores
