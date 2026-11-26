-- Prove2me | solution 1 for BrooksTheorem.colorable_of_cliqueFree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:46:24.462793+00:00
-- url     : https://prove2.me/submissions/d62cdc8d-cfcd-4729-8c0b-3939d9735ba8

module
public import Mathlib
public import Definitions.Def_BrooksLib_BrooksLow
public import Definitions.Def_BrooksLib_Brooks
public import Theorems.Thm_BrooksTheorem_Aux_exists_proper
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
attribute [local simp] BrooksTheorem.Aux.mem_nb
attribute [local simp] BrooksTheorem.Aux.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BrooksTheorem
variable {V : Type*}
namespace BrooksTheorem
theorem _root_.solution [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 3 ≤ k) (hΔ : G.maxDegree ≤ k) (hK : G.CliqueFree (k + 1)) : G.Colorable k := by
  classical
  have hnb : ∀ v, Aux.nb G v = G.neighborFinset v := by intro v; ext u; simp [Aux.nb]
  obtain ⟨f, hf⟩ := Aux.exists_proper k hk G
    (fun v => by rw [hnb, card_neighborFinset_eq_degree]; exact (G.degree_le_maxDegree v).trans hΔ)
    hK
  exact ⟨Coloring.mk f (fun h => hf _ _ h)⟩
end BrooksTheorem
