-- Prove2me | solution 1 for C6BipartiteDomination.compensation_vertex_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:29.009284+00:00
-- url     : https://prove2.me/submissions/d49da9da-4a54-4202-9438-501d8324ffb7

import Definitions.Def_C6BipartiteDomination_A8
import Definitions.Def_C6BipartiteDomination_A9
import Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
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
    {D X : Finset V} {u w q : V}
    (hDom : Dominates G D)
    (hX : X ⊆ Z0Part G D)
    (huB : u ∈ BPart G D)
    (hq : q ∈ compensationRegion G D X u w) :
    q ∉ D ∧ G.Adj q u ∧
      neighborhoodIn G D q ⊆ X ∪ {u} ∧
      (neighborhoodIn G D q).Nonempty := by
  classical
  let T := X ∪ {u}
  have hqR : q ∈ responsibilityRegion G D T :=
    (Finset.mem_sdiff.mp hq).1
  have hqX : q ∉ X := (Finset.mem_sdiff.mp hq).2
  have huD : u ∈ D := (mem_BPart G D u).mp huB |>.1
  have huNotZ : u ∉ ZPart G D := (mem_BPart G D u).mp huB |>.2
  have huNoniso : ∃ v ∈ D, G.Adj u v := by
    by_contra hn
    apply huNotZ
    rw [mem_ZPart]
    refine ⟨huD, ?_⟩
    intro v hv huv
    exact hn ⟨v, hv, huv⟩
  have hqNotD : q ∉ D := by
    intro hqD
    have hqNotRet := (mem_responsibilityRegion G D T q).mp hqR |>.1
    have hqT : q ∈ T := by
      by_contra hqT
      exact hqNotRet (Finset.mem_sdiff.mpr ⟨hqD, hqT⟩)
    have hqEq : q = u := by
      rcases Finset.mem_union.mp hqT with hqX' | hqU
      · exact (hqX hqX').elim
      · exact Finset.mem_singleton.mp hqU
    subst q
    obtain ⟨v, hvD, huv⟩ := huNoniso
    have hvNotX : v ∉ X := by
      intro hvX
      have hvZ0 := hX hvX
      have hvZ := (mem_Z0Part G D v).mp hvZ0 |>.1
      have hvIso := (mem_ZPart G D v).mp hvZ
      exact hvIso.2 u huD huv.symm
    have hvNeU : v ≠ u := by
      intro heq
      subst v
      exact G.irrefl huv
    have hvRet : v ∈ D \ T := by
      refine Finset.mem_sdiff.mpr ⟨hvD, ?_⟩
      intro hvT
      rcases Finset.mem_union.mp hvT with hvX | hvU
      · exact hvNotX hvX
      · exact hvNeU (Finset.mem_singleton.mp hvU)
    exact ((mem_responsibilityRegion G D T u).mp hqR).2 v hvRet huv.symm
  have hqNsub : neighborhoodIn G D q ⊆ T := by
    intro d hd
    have hdN := (mem_neighborhoodIn G D q d).mp hd
    have hqNoRet := (mem_responsibilityRegion G D T q).mp hqR |>.2 d
    by_contra hdT
    exact hqNoRet (Finset.mem_sdiff.mpr ⟨hdN.1, hdT⟩) hdN.2.symm
  have hqNne : (neighborhoodIn G D q).Nonempty := by
    obtain ⟨d, hdD, hdAdj⟩ := hDom hqNotD
    exact ⟨d, (mem_neighborhoodIn G D q d).mpr ⟨hdD, hdAdj.symm⟩⟩
  have hquN : u ∈ neighborhoodIn G D q := by
    by_contra huN
    have hqW0 : q ∈ W0Part G D := by
      rw [mem_W0Part]
      refine ⟨hqNotD, ?_⟩
      intro b hb hbq
      have hbT : b ∈ T := hqNsub ((mem_neighborhoodIn G D q b).mpr ⟨
        (mem_BPart G D b).mp hb |>.1, hbq.symm⟩)
      rcases Finset.mem_union.mp hbT with hbX | hbU
      · exact (Finset.disjoint_left.mp (Z0_disjoint_B G) (hX hbX) hb).elim
      · exact huN (Finset.mem_singleton.mp hbU ▸
          (mem_neighborhoodIn G D q b).mpr ⟨(mem_BPart G D b).mp hb |>.1,
            hbq.symm⟩)
    obtain ⟨d, hdN⟩ := hqNne
    have hdX : d ∈ X := by
      have hdT := hqNsub hdN
      rcases Finset.mem_union.mp hdT with hdX | hdU
      · exact hdX
      · exact (huN (Finset.mem_singleton.mp hdU ▸ hdN)).elim
    have hdz0 := (mem_Z0Part G D d).mp (hX hdX)
    exact hdz0.2 q hqW0 ((mem_neighborhoodIn G D q d).mp hdN).2.symm
  refine ⟨hqNotD, ?_, ?_, hqNne⟩
  · exact ((mem_neighborhoodIn G D q u).mp hquN).2
  · intro d hd
    rcases Finset.mem_union.mp (hqNsub hd) with hdX | hdU
    · exact Finset.mem_union_left _ hdX
    · exact Finset.mem_union_right _ hdU
end C6BipartiteDomination
