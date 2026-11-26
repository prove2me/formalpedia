-- Prove2me | solution 1 for BrooksTheorem.brooks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:47:46.646258+00:00
-- url     : https://prove2.me/submissions/6ae91696-33e3-46bb-9510-b42d8637dfbd

module
public import Mathlib
public import Definitions.Def_BrooksLib_BrooksLow
public import Definitions.Def_BrooksLib_Brooks
public import Theorems.Thm_BrooksTheorem_colorable_of_cliqueFree
public import Theorems.Thm_BrooksTheorem_Aux_greedy_connected
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_top_of_clique
public import Theorems.Thm_BrooksTheorem_Aux_top_of_low
public import Theorems.Thm_BrooksTheorem_Aux_two_regular_colorable
attribute [local simp] BrooksTheorem.Aux.mem_nb
attribute [local simp] BrooksTheorem.Aux.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BrooksTheorem
variable {V : Type*}
namespace BrooksTheorem
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable G.maxDegree := by
  classical
  have hnb : ∀ v, Aux.nb G v = G.neighborFinset v := by intro v; ext u; simp [Aux.nb]
  have hdeg : ∀ v, (Aux.nb G v).card ≤ G.maxDegree := fun v => by
    rw [hnb, card_neighborFinset_eq_degree]; exact G.degree_le_maxDegree v
  have := hconn.nonempty
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hvd : (Aux.nb G v).card = G.maxDegree := by
    rw [hnb, card_neighborFinset_eq_degree, hv]
  rcases le_or_gt 3 G.maxDegree with h3 | h3
  · exact colorable_of_cliqueFree G _ h3 le_rfl
      (fun K hKc => hK (Aux.top_of_clique G hconn hdeg K hKc))
  · by_cases hdef : ∃ v0, (Aux.nb G v0).card < G.maxDegree
    · obtain ⟨f, hf⟩ := Aux.greedy_connected G hconn _ hdeg hdef
      exact ⟨Coloring.mk f (fun h => hf _ _ h)⟩
    · push Not at hdef
      rcases le_or_gt G.maxDegree 1 with h1 | h1
      · exact absurd (Aux.top_of_low G hconn h1 hdeg v hvd) hK
      · have h2 : G.maxDegree = 2 := by omega
        rw [h2]
        exact Aux.two_regular_colorable G hconn
          (fun w => h2 ▸ le_antisymm (hdeg w) (hdef w)) hC
end BrooksTheorem
