-- Prove2me | solution 1 for C6BipartiteDomination.chosen_repair_beta_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:19.336563+00:00
-- url     : https://prove2.me/submissions/8d70be84-064f-40b8-8317-d3d9eb412d2a

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
import Theorems.Thm_C6BipartiteDomination_repair_of_uniform_remaining_neighbors
import Theorems.Thm_C6BipartiteDomination_two_bool_values_have_equal_pair
import Theorems.Thm_C6BipartiteDomination_bipartiteOn_subset
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_WBPart
import Theorems.Thm_C6BipartiteDomination_supportB_card


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hβ : betaCharge G D w = 3) :
    ∃ u, IsRepairVertex G D w u := by
  classical
  let R := supportB G D w
  have hcard : R.card = 3 := by
    change (supportB G D w).card = 3
    rw [supportB_card, hβ]
  obtain ⟨a, b, d, hab, had, hbd, hR⟩ := Finset.card_eq_three.mp hcard
  have hRsupport : supportB G D w = {a, b, d} := by simpa [R] using hR
  have haR : a ∈ R := by rw [hR]; simp
  have hbR : b ∈ R := by rw [hR]; simp
  have hdR : d ∈ R := by rw [hR]; simp
  have haInfo := Finset.mem_filter.mp (show a ∈ supportB G D w by simpa [R] using haR)
  have hbInfo := Finset.mem_filter.mp (show b ∈ supportB G D w by simpa [R] using hbR)
  have hdInfo := Finset.mem_filter.mp (show d ∈ supportB G D w by simpa [R] using hdR)
  have hwD : w ∉ D := by
    exact (mem_WBPart G D w).mp ((mem_SPart G D w).mp hw |>.1) |>.1
  have hBD : BPart G D ⊆ D := by
    intro v hv
    exact (mem_BPart G D v).mp hv |>.1
  obtain ⟨c, hc⟩ := bipartiteOn_subset G hBD hCan.1.2
  have hequal := two_bool_values_have_equal_pair (c a) (c b) (c d)
  rcases hequal with habc | hacd | hbcd
  · refine ⟨d, ?_⟩
    apply repair_of_uniform_remaining_neighbors G hwD hdInfo.1 hdInfo.2 c hc (c a)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset d _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    rw [hRsupport] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h | h
    · exact h ▸ rfl
    · exact h ▸ habc.symm
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
  · refine ⟨b, ?_⟩
    apply repair_of_uniform_remaining_neighbors G hwD hbInfo.1 hbInfo.2 c hc (c a)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset b _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    rw [hRsupport] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h | h
    · exact h ▸ rfl
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
    · exact h ▸ hacd.symm
  · refine ⟨a, ?_⟩
    apply repair_of_uniform_remaining_neighbors G hwD haInfo.1 haInfo.2 c hc (c b)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset a _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    rw [hRsupport] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h | h
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
    · exact h ▸ rfl
    · exact h ▸ hbcd.symm
end C6BipartiteDomination
