-- Prove2me | solution 1 for BrooksTheorem.Aux.top_of_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:39:37.13797+00:00
-- url     : https://prove2.me/submissions/45dad767-192c-43db-a107-53e626faf5c6

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
public import Definitions.Def_BrooksLib_BrooksLow
public import Theorems.Thm_BrooksTheorem_Aux_top_of_clique
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
theorem _root_.solution (G : SimpleGraph V) (hconn : G.Connected) {d : ℕ} (hd : d ≤ 1)
    (hdeg : ∀ v, (nb G v).card ≤ d) (v : V) (hv : (nb G v).card = d) : G = ⊤ := by
  classical
  refine top_of_clique G hconn hdeg (insert v (nb G v)) ?_
  rw [isNClique_iff]
  refine ⟨?_, ?_⟩
  · rw [coe_insert, isClique_insert]
    refine ⟨fun a ha b hb hab => ?_, fun b hb _ => mem_nb.1 hb⟩
    exact absurd (card_le_one.1 (hv ▸ hd) a ha b hb) hab
  · rw [card_insert_of_notMem (by simp), hv]
end BrooksTheorem.Aux
