-- Prove2me | solution 1 for FairChores.cbarSum_univ_le_sum_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:19:30.352052+00:00
-- url     : https://prove2.me/submissions/b86793c6-7bc6-4fa0-b455-532e8ba8466a

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbar_le_cost
import Theorems.Thm_FairChores_cbar_le_price
import Theorems.Thm_FairChores_Outcome_sum_split
attribute [local simp] FairChores.cbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
theorem _root_.solution {o : Outcome T n} (hvalid : o.Valid p) :
    cbarSum c p Finset.univ ≤ ∑ j, cost c o j := by
  classical
  have hsplit := Outcome.sum_split hvalid (cbar c p)
  have h1 : ∑ j, cost c o j
      = (∑ j, ∑ t ∈ o.kept j, c t) + ∑ j, o.pay j := by
    simp [cost, Finset.sum_add_distrib]
  have h2 : ∑ t ∈ o.outsourced, cbar c p t ≤ ∑ t ∈ o.outsourced, p t :=
    Finset.sum_le_sum fun t _ => cbar_le_price t
  have h3 : ∀ j, ∑ t ∈ o.kept j, cbar c p t ≤ ∑ t ∈ o.kept j, c t :=
    fun j => Finset.sum_le_sum fun t _ => cbar_le_cost t
  have h4 : ∑ j, ∑ t ∈ o.kept j, cbar c p t ≤ ∑ j, ∑ t ∈ o.kept j, c t :=
    Finset.sum_le_sum fun j _ => h3 j
  have h5 := hvalid.2.2.2.2
  simp only [cbarSum]
  rw [hsplit, h1]
  linarith
end FairChores
