-- Prove2me | solution 1 for C6BipartiteDomination.bipartite_replacement_of_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:49:13.788957+00:00
-- url     : https://prove2.me/submissions/aac1de04-7895-4c7a-baee-c9f0c4eb6a5c

import Definitions.Def_C6BipartiteDomination_A6
import Definitions.Def_C6BipartiteDomination_A7
import Theorems.Thm_C6BipartiteDomination_selected_Z_isolated
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_ZPart


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V} {w : V}
    (hX : X ⊆ ZPart G D) (hwD : w ∉ D)
    (hbase : IsBipartiteOn G (BPart G D ∪ {w})) :
    IsBipartiteOn G ((D \ X) ∪ {w}) := by
  classical
  rcases hbase with ⟨c, hc⟩
  have hwZ : w ∉ ZPart G D := by
    intro hz
    exact hwD ((mem_ZPart G D w).mp hz).1
  refine ⟨fun v => if v ∈ ZPart G D then !(c w) else c v, ?_⟩
  intro u v hu hv hadj
  have hu' : u ∈ D \ X ∨ u = w := by
    simpa only [Finset.mem_union, Finset.mem_singleton] using hu
  have hv' : v ∈ D \ X ∨ v = w := by
    simpa only [Finset.mem_union, Finset.mem_singleton] using hv
  rcases hu' with huK | huW
  · rcases hv' with hvK | hvW
    · have huD := (Finset.mem_sdiff.mp huK).1
      have hvD := (Finset.mem_sdiff.mp hvK).1
      by_cases huZ : u ∈ ZPart G D
      · exact (selected_Z_isolated G huZ hvD hadj).elim
      · by_cases hvZ : v ∈ ZPart G D
        · exact (selected_Z_isolated G hvZ huD hadj.symm).elim
        · have huB : u ∈ BPart G D := by
            rw [mem_BPart]
            exact ⟨huD, huZ⟩
          have hvB : v ∈ BPart G D := by
            rw [mem_BPart]
            exact ⟨hvD, hvZ⟩
          exact (hc (Finset.mem_union_left _ huB)
            (Finset.mem_union_left _ hvB) hadj)
            |> (fun h => by simpa [huZ, hvZ] using h)
    · subst v
      have huD := (Finset.mem_sdiff.mp huK).1
      by_cases huZ : u ∈ ZPart G D
      · simpa [huZ, hwZ]
      · have huB : u ∈ BPart G D := by
          rw [mem_BPart]
          exact ⟨huD, huZ⟩
        have hbase' := hc (Finset.mem_union_left _ huB)
          (Finset.mem_union_right _ (by simp)) hadj
        simpa [huZ, hwZ] using hbase'
  · subst u
    rcases hv' with hvK | hvW
    · have hvD := (Finset.mem_sdiff.mp hvK).1
      by_cases hvZ : v ∈ ZPart G D
      · have hflip : (if v ∈ ZPart G D then !(c w) else c v) ≠ c w := by
          simp [hvZ, hwZ]
        simpa [hvZ, hwZ] using hflip
      · have hvB : v ∈ BPart G D := by
          rw [mem_BPart]
          exact ⟨hvD, hvZ⟩
        have hbase' := hc (Finset.mem_union_right _ (by simp))
          (Finset.mem_union_left _ hvB) hadj
        simpa [hvZ, hwZ] using hbase'
    · subst v
      exact (G.irrefl hadj).elim
end C6BipartiteDomination
