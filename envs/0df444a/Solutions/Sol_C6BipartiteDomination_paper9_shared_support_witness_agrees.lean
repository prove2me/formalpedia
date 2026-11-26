-- Prove2me | solution 1 for C6BipartiteDomination.paper9_shared_support_witness_agrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:03:35.84983+00:00
-- url     : https://prove2.me/submissions/376dd648-b6e0-4547-81dc-7d2eef93da24

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_sharedCompensation


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X Y : Finset V} {u q : V}
    (huB : u ∈ BPart G D)
    (hX : X ⊆ Z0Part G D) (hY : Y ⊆ Z0Part G D)
    (hqX : q ∈ sharedCompensation G D X u)
    (hqY : q ∈ sharedCompensation G D Y u) :
    ∃ z, z ∈ X ∧ z ∈ Y ∧ neighborhoodIn G D q = {u, z} := by
  classical
  obtain ⟨z₁, hz₁, hN₁⟩ := (mem_sharedCompensation G D X u q).mp hqX |>.2
  obtain ⟨z₂, hz₂, hN₂⟩ := (mem_sharedCompensation G D Y u q).mp hqY |>.2
  have hz₁0 := hX hz₁
  have hz₂0 := hY hz₂
  have hz₁NeU : z₁ ≠ u := by
    intro hEq
    subst z₁
    exact (Finset.disjoint_left.mp (Z0_disjoint_B G (D := D)) hz₁0 huB).elim
  have hz₁Pair : z₁ ∈ ({u, z₂} : Finset V) := by
    have hz₁N : z₁ ∈ neighborhoodIn G D q := by rw [hN₁]; simp
    rw [hN₂] at hz₁N
    exact hz₁N
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz₁Pair
  have hzEq : z₁ = z₂ := by
    rcases hz₁Pair with hzu | hzz
    · exact False.elim (hz₁NeU hzu)
    · exact hzz
  subst z₂
  exact ⟨z₁, hz₁, hz₂, hN₁⟩
end C6BipartiteDomination
