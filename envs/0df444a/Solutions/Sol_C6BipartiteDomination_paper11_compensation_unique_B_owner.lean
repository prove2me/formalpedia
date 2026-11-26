-- Prove2me | solution 1 for C6BipartiteDomination.paper11_compensation_unique_B_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:56:51.072626+00:00
-- url     : https://prove2.me/submissions/24dd2a55-0535-4226-b69c-cb4a43c048a7

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_mem_BPart
import Theorems.Thm_C6BipartiteDomination_mem_sharedCompensation


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D X Y : Finset V} {u v q : V}
    (hX : X ⊆ Z0Part G D) (hY : Y ⊆ Z0Part G D)
    (huB : u ∈ BPart G D) (hvB : v ∈ BPart G D)
    (hqU : q ∈ sharedCompensation G D X u)
    (hqV : q ∈ sharedCompensation G D Y v) : u = v := by
  classical
  obtain ⟨_, ⟨z, hzX, hNz⟩⟩ := (mem_sharedCompensation G D X u q).mp hqU
  obtain ⟨_, ⟨z', hzY, hNz'⟩⟩ := (mem_sharedCompensation G D Y v q).mp hqV
  have hvD := (mem_BPart G D v).mp hvB |>.1
  have hvN : v ∈ neighborhoodIn G D q := by
    rw [hNz']
    simp
  have hvPair : v ∈ ({u, z} : Finset V) := by
    rw [← hNz]
    exact hvN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvPair
  rcases hvPair with hvu | hvz
  · exact hvu.symm
  · subst v
    have hz0 : z ∈ Z0Part G D := hX hzX
    exact False.elim ((Finset.disjoint_left.mp (Z0_disjoint_B G) hz0 hvB).elim)
end C6BipartiteDomination
