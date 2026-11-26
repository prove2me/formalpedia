-- Prove2me | solution 1 for C6BipartiteDomination.lemma_7_1_odd_cycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:01.649468+00:00
-- url     : https://prove2.me/submissions/616204fc-d37a-410a-b135-e20198fa19f6

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_mem_supportX
import Theorems.Thm_C6BipartiteDomination_supportX_card
import Theorems.Thm_C6BipartiteDomination_bipartite_replacement_of_base
import Theorems.Thm_C6BipartiteDomination_collective_exchange
import Theorems.Thm_C6BipartiteDomination_lemma_5_1_responsibility_eq
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_WBPart
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V} (hw : w ∈ SPart G D)
    (hk : 2 ≤ kCharge G D w) :
    ¬ IsBipartiteOn G (BPart G D ∪ {w}) := by
  classical
  intro hbase
  let X := supportX G D w
  let E := (D \ X) ∪ {w}
  have hXZ0 : X ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have hXZ : X ⊆ ZPart G D := by
    intro z hz
    exact (mem_Z0Part G D z).mp (hXZ0 hz) |>.1
  have hRegion := lemma_5_1_responsibility_eq G hCan.1 hXZ0
  have hCover : ∀ ⦃v⦄, Responsible G D X v →
      v ∈ ({w} : Finset V) ∨ ∃ y ∈ ({w} : Finset V), G.Adj y v := by
    intro v hv
    have hvX : v ∈ X := by
      have hvR : v ∈ responsibilityRegion G D X :=
        (mem_responsibilityRegion G D X v).2 hv
      rw [hRegion] at hvR
      exact hvR
    rcases (mem_supportX G D w v).mp hvX with ⟨_, hvw⟩
    by_cases heq : v = w
    · exact Or.inl (by simpa [heq])
    · exact Or.inr ⟨w, by simp, hvw⟩
  have hbip : IsBipartiteOn G E := by
    have hwNotD : w ∉ D := by
      have hwWB := (mem_SPart G D w).mp hw |>.1
      exact (mem_WBPart G D w).mp hwWB |>.1
    exact bipartite_replacement_of_base G hXZ hwNotD hbase
  have hNew : IsBipartiteDominatingSet G E := by
    have := collective_exchange G hCover hbip
    simpa [E] using this
  have hMin := hCan.2.1 E hNew
  have hXsubD : X ⊆ D := by
    intro z hz
    exact (mem_ZPart G D z).mp (hXZ hz) |>.1
  have hXcard : X.card = kCharge G D w := supportX_card G D w
  have hDcard : (D \ X).card + X.card = D.card :=
    Finset.card_sdiff_add_card_eq_card hXsubD
  have hEcard : E.card + X.card = D.card + 1 := by
    have hwNotD : w ∉ D := by
      have := (mem_SPart G D w).mp hw |>.1
      exact (mem_WBPart G D w).mp this |>.1
    have hdisj : Disjoint (D \ X) ({w} : Finset V) := by
      rw [Finset.disjoint_singleton_right]
      intro h
      exact hwNotD ((Finset.mem_sdiff.mp h).1)
    rw [show E = (D \ X) ∪ ({w} : Finset V) by rfl]
    rw [Finset.card_union_of_disjoint hdisj]
    simp only [Finset.card_singleton]
    have hdiff := hDcard
    omega
  rw [hXcard] at hEcard
  rw [hXcard] at hDcard
  have hsmall : kCharge G D w < 2 := by omega
  exact (Nat.not_lt_of_ge hk) hsmall
end C6BipartiteDomination
