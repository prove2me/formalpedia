-- Prove2me | solution 1 for C6BipartiteDomination.compensation_has_at_most_one_X_neighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:50:56.521868+00:00
-- url     : https://prove2.me/submissions/e508e685-bd98-460a-bae1-0153abefd6a1

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
import Theorems.Thm_C6BipartiteDomination_bipartite_add_with_single_neighbor
import Theorems.Thm_C6BipartiteDomination_compensation_vertex_properties
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_bipartiteOn_subset
import Theorems.Thm_C6BipartiteDomination_collective_exchange
import Theorems.Thm_C6BipartiteDomination_lemma_5_1_responsibility_eq
import Theorems.Thm_C6BipartiteDomination_mem_BPart
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
    {D X : Finset V} {u w q x y : V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hX : X ⊆ Z0Part G D)
    (huB : u ∈ BPart G D)
    (hq : q ∈ compensationRegion G D X u w)
    (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    ¬ (G.Adj q x ∧ G.Adj q y) := by
  classical
  intro hqxy
  let Y : Finset V := neighborhoodIn G D q ∩ X
  have hxY : x ∈ Y := by
    simp only [Y, Finset.mem_inter]
    exact ⟨(mem_neighborhoodIn G D q x).mpr ⟨
      (mem_ZPart G D x).mp ((mem_Z0Part G D x).mp (hX hx) |>.1) |>.1,
      hqxy.1⟩, hx⟩
  have hyY : y ∈ Y := by
    simp only [Y, Finset.mem_inter]
    exact ⟨(mem_neighborhoodIn G D q y).mpr ⟨
      (mem_ZPart G D y).mp ((mem_Z0Part G D y).mp (hX hy) |>.1) |>.1,
      hqxy.2⟩, hy⟩
  have hYsubX : Y ⊆ X := by
    exact Finset.inter_subset_right
  have hYsubD : Y ⊆ D := by
    intro z hz
    have hzX := hYsubX hz
    exact (mem_ZPart G D z).mp
      ((mem_Z0Part G D z).mp (hX hzX) |>.1) |>.1
  have hYreg : responsibilityRegion G D Y = Y :=
    lemma_5_1_responsibility_eq G hCan.1 (hYsubX.trans hX)
  have hprops := compensation_vertex_properties G hCan.1.1 hX huB hq
  have hqD := hprops.1
  have hqu := hprops.2.1
  have hqNsub := hprops.2.2.1
  have hqNotY : q ∉ Y := by
    intro hqY
    have hqN := (Finset.mem_inter.mp hqY).1
    exact hqD ((mem_neighborhoodIn G D q q).mp hqN).1
  have hS : IsBipartiteOn G (D \ Y) :=
    bipartiteOn_subset G Finset.sdiff_subset hCan.1.2
  have huS : u ∈ D \ Y := by
    refine Finset.mem_sdiff.mpr ⟨(mem_BPart G D u).mp huB |>.1, ?_⟩
    intro huY
    have huXY := hYsubX huY
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hX huXY) huB)
  have hqAdjU : G.Adj q u := hqu
  have hqOnlyU : ∀ v ∈ D \ Y, G.Adj q v → v = u := by
    intro v hv hadj
    have hvND : v ∈ neighborhoodIn G D q :=
      (mem_neighborhoodIn G D q v).mpr ⟨(Finset.mem_sdiff.mp hv).1, hadj⟩
    have hvXT := hqNsub hvND
    rcases Finset.mem_union.mp hvXT with hvX | hvU
    · have hvY : v ∈ Y := by
        exact Finset.mem_inter.mpr ⟨hvND, hvX⟩
      exact (Finset.mem_sdiff.mp hv).2 hvY |>.elim
    · exact Finset.mem_singleton.mp hvU
  have hbip : IsBipartiteOn G ((D \ Y) ∪ {q}) :=
    bipartite_add_with_single_neighbor G hS huS hqAdjU
      (by intro h; exact hqD ((Finset.mem_sdiff.mp h).1)) hqOnlyU
  have hcover : ∀ ⦃v⦄, Responsible G D Y v →
      v ∈ ({q} : Finset V) ∨ ∃ z ∈ ({q} : Finset V), G.Adj z v := by
    intro v hv
    have hvY : v ∈ Y := by
      have hvR : v ∈ responsibilityRegion G D Y :=
        (mem_responsibilityRegion G D Y v).mpr hv
      rw [hYreg] at hvR
      exact hvR
    have hvX := hYsubX hvY
    have hvN := (Finset.mem_inter.mp hvY).1
    have hadj : G.Adj q v := (mem_neighborhoodIn G D q v).mp hvN |>.2
    exact Or.inr ⟨q, by simp, hadj⟩
  have hnew : IsBipartiteDominatingSet G ((D \ Y) ∪ {q}) :=
    collective_exchange G hcover hbip
  have hYcard : 2 ≤ Y.card := by
    have hpair : ({x, y} : Finset V) ⊆ Y := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hzx | hzy
      · exact hzx ▸ hxY
      · exact hzy ▸ hyY
    have hcard := Finset.card_le_card hpair
    simpa [hxy] using hcard
  have hcardD : (D \ Y).card + Y.card = D.card :=
    Finset.card_sdiff_add_card_eq_card hYsubD
  have hdisj : Disjoint (D \ Y) ({q} : Finset V) := by
    rw [Finset.disjoint_singleton_right]
    intro hqRet
    exact hqD (Finset.mem_sdiff.mp hqRet).1
  have hcardNew : ((D \ Y) ∪ ({q} : Finset V)).card + Y.card = D.card + 1 := by
    rw [Finset.card_union_of_disjoint hdisj]
    simp only [Finset.card_singleton]
    omega
  have hminimal := hCan.2.1 ((D \ Y) ∪ {q}) hnew
  omega
end C6BipartiteDomination
