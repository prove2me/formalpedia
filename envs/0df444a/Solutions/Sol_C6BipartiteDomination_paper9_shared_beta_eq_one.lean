-- Prove2me | solution 1 for C6BipartiteDomination.paper9_shared_beta_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:54:43.590392+00:00
-- url     : https://prove2.me/submissions/d089170d-0838-40c3-8e0b-3d636d1d96b6

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_Z0Part
import Theorems.Thm_C6BipartiteDomination_mem_ZPart
import Theorems.Thm_C6BipartiteDomination_mem_neighborhoodIn
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
    betaCharge G D q = 1 := by
  classical
  have hqInfo := (mem_sharedCompensation G D X u q).mp hq
  obtain ⟨z, hzX, hN⟩ := hqInfo.2
  have hz0 := hX hzX
  have hzNeU : z ≠ u := by
    intro hEq
    subst z
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 huB).elim
  have huD := (mem_BPart G D u).mp huB |>.1
  have hzD := (mem_ZPart G D z).mp ((mem_Z0Part G D z).mp hz0 |>.1) |>.1
  have huAdj : G.Adj q u := by
    have hm : u ∈ ({u, z} : Finset V) := by simp
    have hn : u ∈ neighborhoodIn G D q := by rw [hN]; exact hm
    exact (mem_neighborhoodIn G D q u).mp hn |>.2
  have hfilter : (BPart G D).filter (fun b => G.Adj q b) = {u} := by
    ext b
    constructor
    · intro hb
      have hbB := (Finset.mem_filter.mp hb).1
      have hbD := (mem_BPart G D b).mp hbB |>.1
      have hbN : b ∈ neighborhoodIn G D q :=
        (mem_neighborhoodIn G D q b).mpr
          ⟨hbD, (Finset.mem_filter.mp hb).2⟩
      have hbPair : b ∈ ({u, z} : Finset V) := by rw [← hN]; exact hbN
      simp only [Finset.mem_insert, Finset.mem_singleton] at hbPair
      rcases hbPair with hbu | hbz
      · simpa [hbu]
      · subst b
        exact False.elim ((Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 hbB).elim)
    · intro hb
      have hbEq : b = u := Finset.mem_singleton.mp hb
      subst b
      exact Finset.mem_filter.mpr ⟨huB, huAdj⟩
  unfold betaCharge degreeTo
  rw [hfilter]
  simp
end C6BipartiteDomination
