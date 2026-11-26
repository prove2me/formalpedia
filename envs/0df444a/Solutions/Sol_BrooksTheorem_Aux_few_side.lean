-- Prove2me | solution 1 for BrooksTheorem.Aux.few_side
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:12.111933+00:00
-- url     : https://prove2.me/submissions/a7df57cb-0aba-4cd8-a862-ab7d8e1220d8

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
public import Theorems.Thm_BrooksTheorem_Aux_colour_restr
public import Theorems.Thm_BrooksTheorem_Aux_proper_update2
public import Theorems.Thm_BrooksTheorem_Aux_exists_not_mem_of_card_lt
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
attribute [local simp] BrooksTheorem.Aux.mem_nb


attribute [local simp] BrooksTheorem.Aux.restr_adj

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (S : Set V) {x z qx qz w : V}
    (hn : ¬ H.Adj x z) (hw : H.Adj x w)
    (hx1 : ∀ v ∈ S, v ≠ z → H.Adj x v → v = qx) (hz1 : ∀ v ∈ S, v ≠ x → H.Adj z v → v = qz) :
    ∃ c : V → Fin k, Proper (restr H S) c ∧ c x = c z := by
  classical
  obtain ⟨c0, hc0⟩ := colour_restr ih hdeg hcf {v | v ∈ S ∧ v ≠ x ∧ v ≠ z} hw
    (fun h => h.2.1 rfl)
  have h2 : ({c0 qx, c0 qz} : Finset (Fin k)).card < k :=
    lt_of_le_of_lt (card_le_two) (by omega)
  obtain ⟨col, hcol⟩ := exists_not_mem_of_card_lt _ h2
  refine ⟨_, proper_update2 S hn c0 hc0 col ?_, by simp⟩
  intro w' v hw' hvS hvx hvz hwv he
  apply hcol
  rcases hw' with rfl | rfl
  · rw [hx1 v hvS hvz hwv] at he; simp [he]
  · rw [hz1 v hvS hvx hwv] at he; simp [he]
end BrooksTheorem.Aux
