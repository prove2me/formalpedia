-- Prove2me | solution 1 for C6BipartiteDomination.lemma_8_4_compensation_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:52:14.54392+00:00
-- url     : https://prove2.me/submissions/c630e1d5-8572-45ad-becc-e3f4ac7c2852

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
import Theorems.Thm_C6BipartiteDomination_mem_privateCompensation
import Theorems.Thm_C6BipartiteDomination_mem_sharedCompensation
import Theorems.Thm_C6BipartiteDomination_compensation_vertex_properties
import Theorems.Thm_C6BipartiteDomination_compensation_has_at_most_one_X_neighbor
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion
import Theorems.Thm_C6BipartiteDomination_mem_supportX


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    {w : V}
    {R : Finset V} {u : V}
    (hChosen : ChosenRepairRelation G D w R u) :
    let X := supportX G D w
    let Q := compensationRegion G D X u w
    Q = privateCompensation G D u ∪ sharedCompensation G D X u ∧
      Disjoint (privateCompensation G D u) (sharedCompensation G D X u) ∧
      ∀ q ∈ Q, q ∉ D ∧ G.Adj u q := by
  classical
  let X := supportX G D w
  let Q := compensationRegion G D X u w
  let T := X ∪ {u}
  have hXsub : X ⊆ Z0Part G D := by
    intro z hz
    exact (mem_supportX G D w z).mp hz |>.1
  have huB : u ∈ BPart G D := hChosen.2.1
  have huD : u ∈ D := (mem_BPart G D u).mp huB |>.1
  have hDom : Dominates G D := hCan.1.1
  have hqProps : ∀ q ∈ Q,
      q ∉ D ∧ G.Adj q u ∧ neighborhoodIn G D q ⊆ X ∪ {u} ∧
        (neighborhoodIn G D q).Nonempty := by
    intro q hq
    exact compensation_vertex_properties G hDom hXsub huB hq
  have hNoTwo : ∀ q ∈ Q, ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      ¬ (G.Adj q x ∧ G.Adj q y) := by
    intro q hq x hx y hy hxy
    exact compensation_has_at_most_one_X_neighbor G hCan hXsub huB hq hx hy hxy
  have hQeq : Q = privateCompensation G D u ∪ sharedCompensation G D X u := by
    ext q
    constructor
    · intro hq
      have hp := hqProps q hq
      have hqD := hp.1
      have hqu := hp.2.1
      have hNsub := hp.2.2.1
      by_cases hex : ∃ z ∈ X, G.Adj q z
      · obtain ⟨z, hzX, hqz⟩ := hex
        have hN : neighborhoodIn G D q = {u, z} := by
          apply Finset.ext
          intro d
          constructor
          · intro hd
            have hdT := hNsub hd
            rcases Finset.mem_union.mp hdT with hdX | hdU
            · have hdAdj := (mem_neighborhoodIn G D q d).mp hd |>.2
              have hdEq : d = z ∨ d = u := by
                by_cases hdeq : d = z
                · exact Or.inl hdeq
                · have := hNoTwo q hq d hdX z hzX hdeq
                  exact (this ⟨hdAdj, hqz⟩).elim
              rcases hdEq with hdEq | hdEq
              · subst d
                simp
              · subst d
                simp
            · have hdEq : d = u := Finset.mem_singleton.mp hdU
              subst d
              simp
          · intro hd
            simp only [Finset.mem_insert, Finset.mem_singleton] at hd
            rcases hd with hd | hd
            · subst d
              exact (mem_neighborhoodIn G D q u).mpr ⟨huD, hqu⟩
            · subst d
              have hzD := (mem_ZPart G D z).mp
                ((mem_Z0Part G D z).mp (hXsub hzX) |>.1) |>.1
              exact (mem_neighborhoodIn G D q z).mpr ⟨hzD, hqz⟩
        exact Finset.mem_union.mpr (Or.inr
          ((mem_sharedCompensation G D X u q).mpr ⟨hqD, z, hzX, hN⟩))
      · have hN : neighborhoodIn G D q = {u} := by
          apply Finset.ext
          intro d
          constructor
          · intro hd
            have hdT := hNsub hd
            rcases Finset.mem_union.mp hdT with hdX | hdU
            · have hdAdj := (mem_neighborhoodIn G D q d).mp hd |>.2
              exact (hex ⟨d, hdX, hdAdj⟩).elim
            · exact Finset.mem_singleton.mpr (Finset.mem_singleton.mp hdU)
          · intro hd
            have hdEq := Finset.mem_singleton.mp hd
            subst d
            exact (mem_neighborhoodIn G D q u).mpr ⟨huD, hqu⟩
        exact Finset.mem_union.mpr (Or.inl
          ((mem_privateCompensation G D u q huD).mpr ⟨hqD, hN⟩))
    · intro h
      rcases Finset.mem_union.mp h with hp | hl
      · have hpi := (mem_privateCompensation G D u q huD).mp hp
        have hnotRet : ∀ d ∈ D \ T, ¬ G.Adj d q := by
          intro d hd hAdj
          have hdN := (mem_neighborhoodIn G D q d).mpr
            ⟨(Finset.mem_sdiff.mp hd).1, hAdj.symm⟩
          have hdEq := Finset.mem_singleton.mp (by simpa [hpi.2] using hdN)
          exact (Finset.mem_sdiff.mp hd).2 (hdEq ▸ Finset.mem_union_right X (by simp))
        have hqD := hpi.1
        have hqX : q ∉ X := by
          intro hqX
          exact hqD ((mem_ZPart G D q).mp
            ((mem_Z0Part G D q).mp (hXsub hqX) |>.1) |>.1)
        have hqQ : q ∈ Q := by
          apply Finset.mem_sdiff.mpr
          refine ⟨(mem_responsibilityRegion G D T q).mpr ?_, hqX⟩
          exact ⟨by
            intro hqRet
            exact hqD (Finset.mem_sdiff.mp hqRet).1,
            hnotRet⟩
        exact hqQ
      · have hli := (mem_sharedCompensation G D X u q).mp hl
        have hqD := hli.1
        obtain ⟨z, hzX, hN⟩ := hli.2
        have hqX : q ∉ X := by
          intro hqX
          exact hqD ((mem_ZPart G D q).mp
            ((mem_Z0Part G D q).mp (hXsub hqX) |>.1) |>.1)
        have hnotRet : ∀ d ∈ D \ T, ¬ G.Adj d q := by
          intro d hd hAdj
          have hdN := (mem_neighborhoodIn G D q d).mpr
            ⟨(Finset.mem_sdiff.mp hd).1, hAdj.symm⟩
          have hdEq : d = u ∨ d = z := by
            have hmem : d ∈ ({u, z} : Finset V) := by simpa [hN] using hdN
            simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
          rcases hdEq with heq | heq
          · exact (Finset.mem_sdiff.mp hd).2 (heq ▸ Finset.mem_union_right X (by simp))
          · have hzT : z ∈ T := Finset.mem_union_left _ hzX
            exact (Finset.mem_sdiff.mp hd).2 (heq ▸ hzT)
        have hqQ : q ∈ Q := by
          apply Finset.mem_sdiff.mpr
          refine ⟨(mem_responsibilityRegion G D T q).mpr ?_, hqX⟩
          exact ⟨by
            intro hqRet
            exact hqD (Finset.mem_sdiff.mp hqRet).1,
            hnotRet⟩
        exact hqQ
  have hdisj : Disjoint (privateCompensation G D u)
      (sharedCompensation G D X u) := by
    rw [Finset.disjoint_left]
    intro q hp hl
    have hpN := (mem_privateCompensation G D u q huD).mp hp |>.2
    obtain ⟨_, z, hzX, hLN⟩ := (mem_sharedCompensation G D X u q).mp hl
    have hzInPair : z ∈ ({u, z} : Finset V) := by simp
    have hzN : z ∈ neighborhoodIn G D q := (Finset.ext_iff.mp hLN z).mpr hzInPair
    have hzD := (mem_ZPart G D z).mp
      ((mem_Z0Part G D z).mp (hXsub hzX) |>.1) |>.1
    have hzAdj := (mem_neighborhoodIn G D q z).mp hzN |>.2
    have hzN' := (mem_neighborhoodIn G D q z).mpr ⟨hzD, hzAdj⟩
    have hzU : z = u := Finset.mem_singleton.mp (by simpa [hpN] using hzN')
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hXsub hzX)
      (hzU ▸ huB)).elim
  have hQneighbors : ∀ q ∈ Q, q ∉ D ∧ G.Adj u q := by
    intro q hq
    have hp := hqProps q hq
    exact ⟨hp.1, hp.2.1.symm⟩
  exact ⟨by simpa [Q] using hQeq, hdisj, by simpa [Q] using hQneighbors⟩
end C6BipartiteDomination
