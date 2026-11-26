-- Prove2me | solution 1 for BrooksTheorem.Aux.proper_update2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:05.703268+00:00
-- url     : https://prove2.me/submissions/0c9750aa-e2f5-4531-91df-0c4dd3953663

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
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
omit [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution [DecidableEq V] {k : ℕ} {H : SimpleGraph V} (S : Set V) {x z : V}
    (hn : ¬ H.Adj x z)
    (c0 : V → Fin k) (hc0 : Proper (restr H {v | v ∈ S ∧ v ≠ x ∧ v ≠ z}) c0) (col : Fin k)
    (hcol : ∀ w v, (w = x ∨ w = z) → v ∈ S → v ≠ x → v ≠ z → H.Adj w v → c0 v ≠ col) :
    Proper (restr H S) (fun v => if v = x ∨ v = z then col else c0 v) := by
  intro u v ⟨huv, hu, hv⟩
  by_cases hux : u = x ∨ u = z <;> by_cases hvx : v = x ∨ v = z
  · exfalso
    have hne := H.ne_of_adj huv
    rcases hux with rfl | rfl <;> rcases hvx with rfl | rfl
    · exact hne rfl
    · exact hn huv
    · exact hn huv.symm
    · exact hne rfl
  · simp only [hux, hvx, ite_true, ite_false]
    push Not at hvx
    exact (hcol u v hux hv hvx.1 hvx.2 huv).symm
  · simp only [hux, hvx, ite_true, ite_false]
    push Not at hux
    exact hcol v u hvx hu hux.1 hux.2 huv.symm
  · simp only [hux, hvx, ite_false]
    push Not at hux hvx
    exact hc0 u v ⟨huv, ⟨hu, hux⟩, ⟨hv, hvx⟩⟩
end BrooksTheorem.Aux
