-- Prove2me | solution 1 for FairChores.wtSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:46.743776+00:00
-- url     : https://prove2.me/submissions/554c054f-976f-4f71-b6d9-8d1e02288652

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_wt_nonneg

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) (hp : ∀ t, 0 ≤ p t) (A : Finset T) :
    0 ≤ wtSum c p mu A :=
  Finset.sum_nonneg fun t _ => wt_nonneg hc hp t
end FairChores
