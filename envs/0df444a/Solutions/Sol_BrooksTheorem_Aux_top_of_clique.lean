-- Prove2me | solution 1 for BrooksTheorem.Aux.top_of_clique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:38:24.592684+00:00
-- url     : https://prove2.me/submissions/601b75bb-8063-4ba6-a960-4d74629013aa

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
public import Definitions.Def_BrooksLib_BrooksLow
public import Theorems.Thm_BrooksTheorem_Aux_mem_of_closed
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
attribute [local simp] BrooksTheorem.Aux.mem_nb
attribute [local simp] BrooksTheorem.Aux.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (G : SimpleGraph V) (hconn : G.Connected) {d : ℕ}
    (hdeg : ∀ v, (nb G v).card ≤ d) (K : Finset V) (hK : G.IsNClique (d + 1) K) : G = ⊤ := by
  classical
  rw [isNClique_iff] at hK
  obtain ⟨hKc, hKcard⟩ := hK
  have hnbK : ∀ v ∈ K, nb G v = K.erase v := by
    intro v hv
    symm
    apply eq_of_subset_of_card_le
    · intro u hu
      rw [mem_erase] at hu
      exact mem_nb.2 (hKc hv hu.2 hu.1.symm)
    · rw [card_erase_of_mem hv, hKcard]
      exact hdeg v
  obtain ⟨v0, hv0⟩ : K.Nonempty := by rw [← card_pos, hKcard]; omega
  have hall : ∀ w, w ∈ (K : Set V) := by
    refine mem_of_closed G hconn (K : Set V) hv0 ?_
    intro u hu w huw
    have : w ∈ nb G u := mem_nb.2 huw
    rw [hnbK u hu] at this
    exact (mem_erase.1 this).2
  ext u w
  simp only [top_adj]
  constructor
  · exact G.ne_of_adj
  · intro huw
    exact hKc (hall u) (hall w) huw
end BrooksTheorem.Aux
