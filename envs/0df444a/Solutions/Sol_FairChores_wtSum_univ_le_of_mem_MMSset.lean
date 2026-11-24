-- Prove2me | solution 1 for FairChores.wtSum_univ_le_of_mem_MMSset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:20:55.687554+00:00
-- url     : https://prove2.me/submissions/b05e72b6-52ae-4537-8a91-600377942311

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbarSum_empty
import Theorems.Thm_FairChores_cbar_le_cost
import Theorems.Thm_FairChores_cbar_le_price
import Theorems.Thm_FairChores_Outcome_sum_split
import Theorems.Thm_FairChores_mem_outsourced_of_lt_cost
attribute [local simp] FairChores.cbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ} {mu : ℝ}
namespace FairChores
theorem _root_.solution (hc : ∀ t, 0 ≤ c t) {r : ℝ}
    (hgap : ∀ t, mu < cbar c p t → r < cbar c p t) (hr : r ∈ MMSset n c p) :
    wtSum c p mu Finset.univ ≤ n * r := by
  classical
  obtain ⟨o, hvalid, hle⟩ := hr
  have hsplit := Outcome.sum_split hvalid (wt c p mu)
  have h1 : ∑ t ∈ o.outsourced, wt c p mu t ≤ ∑ t ∈ o.outsourced, p t :=
    Finset.sum_le_sum fun t _ => by
      unfold wt; split
      · exact le_rfl
      · exact cbar_le_price t
  have h2 : ∀ j, ∑ t ∈ o.kept j, wt c p mu t ≤ ∑ t ∈ o.kept j, c t := by
    intro j
    refine Finset.sum_le_sum fun t ht => ?_
    unfold wt
    split
    · rename_i hexp
      exfalso
      have hgt := hgap t hexp
      have hct : r < c t := lt_of_lt_of_le hgt (cbar_le_cost t)
      have hmem := mem_outsourced_of_lt_cost hvalid hc hle hct
      exact Finset.disjoint_left.mp (hvalid.1 j) hmem ht
    · exact cbar_le_cost t
  have h3 : ∑ j, ∑ t ∈ o.kept j, wt c p mu t ≤ ∑ j, ∑ t ∈ o.kept j, c t :=
    Finset.sum_le_sum fun j _ => h2 j
  have h4 : ∑ j, cost c o j ≤ n * r := by
    calc ∑ j : Fin n, cost c o j ≤ ∑ _j : Fin n, r := Finset.sum_le_sum fun j _ => hle j
      _ = n * r := by simp [mul_comm]
  have h5 : ∑ j, cost c o j = (∑ j, ∑ t ∈ o.kept j, c t) + ∑ j, o.pay j := by
    simp [cost, Finset.sum_add_distrib]
  have h6 := hvalid.2.2.2.2
  simp only [wtSum]
  rw [hsplit]
  linarith
end FairChores
