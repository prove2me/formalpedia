-- Prove2me | solution 1 for C6BipartiteDomination.minimal_deficient_card_ge_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:43:36.259367+00:00
-- url     : https://prove2.me/submissions/23816894-3e6c-403f-a568-a1af873c668e

import Definitions.Def_C6BipartiteDomination_A2
import Definitions.Def_C6BipartiteDomination_A3
import Theorems.Thm_C6BipartiteDomination_mem_neighborsIn
import Theorems.Thm_C6BipartiteDomination_independent_vertex_has_external_neighbor

set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X : Finset V} (hXsub : X ⊆ D)
    (hDind : Independent G D) (hNoIso : HasNoIsolatedVertices G)
    (hdef : (neighborsIn G X (Finset.univ \ D)).card < X.card) :
    2 ≤ X.card := by
  classical
  have hpos : 0 < X.card := Nat.zero_lt_of_lt hdef
  by_contra hnot
  have hsmall : X.card = 0 ∨ X.card = 1 := by omega
  rcases hsmall with hzero | hone
  · have : X = ∅ := Finset.card_eq_zero.mp hzero
    simp [this] at hdef
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
    have hxX : x ∈ X := by rw [hx]; simp
    have hxD : x ∈ D := hXsub hxX
    obtain ⟨w, hw, hadj⟩ := independent_vertex_has_external_neighbor G hDind hNoIso hxD
    have hneigh : w ∈ neighborsIn G X (Finset.univ \ D) := by
      rw [mem_neighborsIn]
      refine ⟨hw, ?_⟩
      exact ⟨x, by simpa [hx], hadj⟩
    have hcard : 0 < (neighborsIn G X (Finset.univ \ D)).card :=
      Finset.card_pos.mpr ⟨w, hneigh⟩
    rw [hone] at hdef
    omega
end C6BipartiteDomination
