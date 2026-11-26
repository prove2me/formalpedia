-- Prove2me | solution 1 for C6BipartiteDomination.paper9_shared_compensation_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:54:14.070916+00:00
-- url     : https://prove2.me/submissions/8a8cac1c-2160-41d7-93e4-b1cfb4815f3b

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_PPart
import Theorems.Thm_C6BipartiteDomination_mem_SPart
import Theorems.Thm_C6BipartiteDomination_mem_W0Part
import Theorems.Thm_C6BipartiteDomination_mem_WBPart
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
import Theorems.Thm_C6BipartiteDomination_mem_privateExternalNeighbors
import Theorems.Thm_C6BipartiteDomination_mem_sharedCompensation


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V} {u q : V}
    (hX : X ⊆ Z0Part G D) (huB : u ∈ BPart G D)
    (hq : q ∈ sharedCompensation G D X u) :
    q ∈ SPart G D ∧ G.Adj u q ∧ kCharge G D q = 1 := by
  classical
  have hqInfo := (mem_sharedCompensation G D X u q).mp hq
  obtain ⟨z, hzX, hN⟩ := hqInfo.2
  have hz0 := hX hzX
  have hzD := (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp hz0 |>.1) |>.1
  have hzNeU : z ≠ u := by
    intro hEq
    subst z
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 huB).elim
  have huD := (mem_BPart G D u).mp huB |>.1
  have hqAdjU : G.Adj q u := by
    have hmem : u ∈ ({u, z} : Finset V) := by simp
    have hmemN : u ∈ neighborhoodIn G D q := by
      rw [hN]
      exact hmem
    exact (mem_neighborhoodIn G D q u).mp hmemN |>.2
  have hqAdjZ : G.Adj q z := by
    have hmem : z ∈ ({u, z} : Finset V) := by simp
    have hmemN : z ∈ neighborhoodIn G D q := by
      rw [hN]
      exact hmem
    exact (mem_neighborhoodIn G D q z).mp hmemN |>.2
  have hqN_z : z ∈ neighborhoodIn G D q := by
    exact (mem_neighborhoodIn G D q z).mpr ⟨hzD, hqAdjZ⟩
  have hqNotP : q ∉ PPart G D := by
    intro hqP
    obtain ⟨b, hbB, hpriv⟩ := (mem_PPart G D q).mp hqP
    have hbD := (mem_BPart G D b).mp hbB |>.1
    have hpriv' := (mem_privateExternalNeighbors G D b q).mp hpriv |>.2
    have hbu : b = u := ((hpriv' u huD).mp hqAdjU.symm).symm
    subst b
    have hzu : z = u := (hpriv' z hzD).mp hqAdjZ.symm
    exact hzNeU hzu
  have hqWB : q ∈ WBPart G D := by
    rw [mem_WBPart]
    refine ⟨hqInfo.1, ?_⟩
    intro hq0
    exact ((mem_W0Part G D q).mp hq0).2 u huB hqAdjU.symm
  have hqS : q ∈ SPart G D := by
    rw [mem_SPart]
    exact ⟨hqWB, hqNotP⟩
  have hfilter : (Z0Part G D).filter (fun x => G.Adj q x) = {z} := by
    ext x
    constructor
    · intro hx
      have hx0 := (Finset.mem_filter.mp hx).1
      have hxD := (mem_ZPart G D x).mp ((mem_Z0Part G D x).mp hx0 |>.1) |>.1
      have hxN : x ∈ neighborhoodIn G D q := by
        exact (mem_neighborhoodIn G D q x).mpr
          ⟨hxD, (Finset.mem_filter.mp hx).2⟩
      have hxPair : x ∈ ({u, z} : Finset V) := by rw [← hN]; exact hxN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxPair
      rcases hxPair with hxU | hxZ
      · subst x
        exact False.elim ((Finset.disjoint_left.mp (Z0_disjoint_B G) hx0 huB).elim)
      · simpa [hxZ]
    · intro hx
      have hxZ : x = z := Finset.mem_singleton.mp hx
      subst x
      exact Finset.mem_filter.mpr ⟨hz0, hqAdjZ⟩
  have hk : kCharge G D q = 1 := by
    unfold kCharge degreeTo
    rw [hfilter]
    simp
  exact ⟨hqS, hqAdjU.symm, hk⟩
end C6BipartiteDomination
