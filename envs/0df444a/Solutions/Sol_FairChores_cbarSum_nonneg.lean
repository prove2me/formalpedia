-- Prove2me | solution 1 for FairChores.cbarSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:18:27.613043+00:00
-- url     : https://prove2.me/submissions/9a97d62a-0b68-41b6-b437-046ffbc1806e

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbar_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (A : Finset T) :
    0 ≤ cbarSum c p A :=
  Finset.sum_nonneg fun t _ => cbar_nonneg hc hp t
end FairChores
