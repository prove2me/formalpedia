-- Prove2me | solution 1 for C6BipartiteDomination.chosen_repairs_beta_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:51:03.127342+00:00
-- url     : https://prove2.me/submissions/04c83525-0a69-4a17-8bce-ba1b43fe7998

import Definitions.Def_C6BipartiteDomination_A7
import Definitions.Def_C6BipartiteDomination_A8
import Theorems.Thm_C6BipartiteDomination_bipartite_add_of_uniform_neighbors
import Theorems.Thm_C6BipartiteDomination_repair_of_uniform_remaining_neighbors
import Theorems.Thm_C6BipartiteDomination_bipartiteOn_subset
import Theorems.Thm_C6BipartiteDomination_lemma_7_1_odd_cycle
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
    (hk : 2 ≤ kCharge G D w) (hβ : betaCharge G D w = 2) :
    ∃ R : Finset V, R.card = 2 ∧
      ∀ u ∈ R, IsRepairVertex G D w u := by
  classical
  let R := supportB G D w
  have hcard : R.card = 2 := by
    change (supportB G D w).card = 2
    rw [supportB_card]
    exact hβ
  obtain ⟨a, b, hab, hR⟩ := Finset.card_eq_two.mp hcard
  have haR : a ∈ R := by rw [hR]; simp
  have hbR : b ∈ R := by rw [hR]; simp
  have haInfo := Finset.mem_filter.mp (show a ∈ supportB G D w by simpa [R] using haR)
  have hbInfo := Finset.mem_filter.mp (show b ∈ supportB G D w by simpa [R] using hbR)
  have hwD : w ∉ D := by
    exact (mem_WBPart G D w).mp ((mem_SPart G D w).mp hw |>.1) |>.1
  have hBD : BPart G D ⊆ D := by
    intro v hv
    exact (mem_BPart G D v).mp hv |>.1
  obtain ⟨c, hc⟩ := bipartiteOn_subset G hBD hCan.1.2
  have hnot := lemma_7_1_odd_cycle G hCan hw hk
  have habColor : c a ≠ c b := by
    intro heq
    have huniform : ∀ v ∈ BPart G D, G.Adj w v → c v = c a := by
      intro v hv hadj
      have hvR : v ∈ R := by
        change v ∈ (BPart G D).filter (fun x => G.Adj w x)
        exact Finset.mem_filter.mpr ⟨hv, hadj⟩
      change v ∈ supportB G D w at hvR
      have hR' : supportB G D w = {a, b} := by simpa [R] using hR
      rw [hR'] at hvR
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
      rcases hvR with h | h
      · exact h ▸ rfl
      · exact h ▸ heq.symm
    have hbase := bipartite_add_of_uniform_neighbors G
      (B := BPart G D) (S := BPart G D) (w := w)
      Finset.Subset.rfl (by
        intro hwB
        exact hwD ((mem_BPart G D w).mp hwB |>.1)) c hc (c a) huniform
    exact hnot hbase
  have hRepairA : IsRepairVertex G D w a := by
    apply repair_of_uniform_remaining_neighbors G hwD haInfo.1 haInfo.2 c hc (c b)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset a _ hv, hadj⟩
    change v ∈ supportB G D w at hvR
    have hR' : supportB G D w = {a, b} := by simpa [R] using hR
    rw [hR'] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
    · exact h ▸ rfl
  have hRepairB : IsRepairVertex G D w b := by
    apply repair_of_uniform_remaining_neighbors G hwD hbInfo.1 hbInfo.2 c hc (c a)
    intro v hv hadj
    have hvR : v ∈ R := by
      change v ∈ (BPart G D).filter (fun x => G.Adj w x)
      exact Finset.mem_filter.mpr ⟨Finset.erase_subset b _ hv, hadj⟩
    rw [hR] at hvR
    simp only [Finset.mem_insert, Finset.mem_singleton] at hvR
    rcases hvR with h | h
    · exact h ▸ rfl
    · exact False.elim ((Finset.mem_erase.mp hv).1 h)
  refine ⟨R, hcard, ?_⟩
  intro u hu
  have hu' : u = a ∨ u = b := by
    rw [hR] at hu
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hu
  rcases hu' with rfl | rfl
  · exact hRepairA
  · exact hRepairB
end C6BipartiteDomination
