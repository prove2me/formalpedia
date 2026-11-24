-- Prove2me | solution 1 for FairChores.single_le_cbarSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:26.624435+00:00
-- url     : https://prove2.me/submissions/dde2ffe7-ace7-4760-9a88-2582011cbdb0

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
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) {A : Finset T} {t : T}
    (ht : t ∈ A) : cbar c p t ≤ cbarSum c p A :=
  Finset.single_le_sum (fun s _ => cbar_nonneg hc hp s) ht
end FairChores
