-- Prove2me | solution 1 for Expanders.vertexBall_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:40:12.764374+00:00
-- url     : https://prove2.me/submissions/8af9e15d-ff1d-4de8-ac62-2e579e5589d5

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
public import Theorems.Thm_Expanders_dist_adj_le
public import Theorems.Thm_Expanders_exists_adj_dist_lt
public import Theorems.Thm_Expanders_mem_vertexBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
variable {G : SimpleGraph V} {u : V} {k : ℕ}
namespace Expanders
theorem _root_.solution [DecidableRel G.Adj] {d : ℕ} (hd : G.IsRegularOfDegree d) (hd1 : 1 ≤ d) :
    ∀ v ∈ vertexBall G u k, ∃ w ∈ vertexBall G u k, G.Adj v w ∧
      G.dist u w - 1 ≤ G.dist u v - 1 - 1 := by
  intro v hv
  rw [mem_vertexBall] at hv
  by_cases h0 : G.dist u v = 0
  · have hvu : u = v := (hv.1.dist_eq_zero_iff).mp h0
    subst hvu
    have hne : (G.neighborFinset u).Nonempty := by
      rw [← Finset.card_pos, card_neighborFinset_eq_degree, hd u]; omega
    obtain ⟨w, hw⟩ := hne
    rw [mem_neighborFinset] at hw
    have h1 := dist_adj_le (Reachable.refl u) hw
    simp only [SimpleGraph.dist_self] at h1
    exact ⟨w, mem_vertexBall.mpr ⟨hw.reachable, by omega⟩, hw, by omega⟩
  · obtain ⟨w, hvw, huw, hlt⟩ := exists_adj_dist_lt hv.1 h0
    exact ⟨w, mem_vertexBall.mpr ⟨huw, by omega⟩, hvw, by omega⟩
end Expanders
