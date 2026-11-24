-- Prove2me | solution 1 for FairChores.mem_outsourced_of_lt_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:25.572195+00:00
-- url     : https://prove2.me/submissions/de342948-5d97-44fc-bdbe-a4ff8c654024

import Mathlib
import Definitions.Def_RequestProject_ChoresModel
import Theorems.Thm_FairChores_cbarSum_empty
attribute [local simp] FairChores.cbarSum_empty

set_option autoImplicit true
open scoped BigOperators
open FairChores
variable {T : Type*} [Fintype T] [DecidableEq T]
variable {n : ℕ}
variable {c p : T → ℝ}
namespace FairChores
theorem _root_.solution {o : Outcome T n} (hvalid : o.Valid p) (hc : ∀ t, 0 ≤ c t)
    {r : ℝ} (hle : ∀ j, cost c o j ≤ r) {t : T} (ht : r < c t) : t ∈ o.outsourced := by
  classical
  by_contra hnot
  have hmem : t ∈ o.outsourced ∪ Finset.univ.biUnion o.kept := by
    rw [hvalid.2.2.1]; exact Finset.mem_univ t
  rcases Finset.mem_union.mp hmem with h | h
  · exact hnot h
  · obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp h
    have h1 : c t ≤ ∑ s ∈ o.kept j, c s :=
      Finset.single_le_sum (fun s _ => hc s) hj
    have h2 := hvalid.2.2.2.1 j
    have h3 := hle j
    simp only [cost] at h3
    linarith
end FairChores
