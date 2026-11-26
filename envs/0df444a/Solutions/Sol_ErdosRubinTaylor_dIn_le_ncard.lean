-- Prove2me | solution 1 for ErdosRubinTaylor.dIn_le_ncard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:30:23.798284+00:00
-- url     : https://prove2.me/submissions/e61b9ddb-7148-4ff3-b9ed-1d9dc4ef7721

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Theorems.Thm_ErdosRubinTaylor_dIn_eq
public import Theorems.Thm_ErdosRubinTaylor_ncard_eq_filter

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
namespace ErdosRubinTaylor
theorem _root_.solution (G : SimpleGraph V) (T : Set V) {v : V} (hv : v ∈ T) :
    dIn G T v ≤ T.ncard - 1 := by
  classical
  rw [dIn_eq, ncard_eq_filter]
  have hsub : univ.filter (fun u => u ∈ T ∧ G.Adj v u) ⊆ (univ.filter (· ∈ T)).erase v := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and, mem_erase] at hu ⊢
    exact ⟨(G.ne_of_adj hu.2).symm, hu.1⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (by simpa using hv)] at this
  exact this
end ErdosRubinTaylor
