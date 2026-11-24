-- Prove2me | solution 1 for FairChores.cbarSum_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:23.733854+00:00
-- url     : https://prove2.me/submissions/d60c18d3-aa4a-497a-abea-dbd670b164fc

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbar_le_cost

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
omit [Fintype T] [DecidableEq T]
namespace FairChores
theorem _root_.solution (c p : T → ℝ) (A : Finset T) : cbarSum c p A ≤ ∑ t ∈ A, c t :=
  Finset.sum_le_sum fun t _ => cbar_le_cost t
end FairChores
