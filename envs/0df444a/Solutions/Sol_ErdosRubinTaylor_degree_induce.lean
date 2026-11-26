-- Prove2me | solution 1 for ErdosRubinTaylor.degree_induce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:34:20.325688+00:00
-- url     : https://prove2.me/submissions/0d92d596-7ca3-4107-bbe2-7bcdad34c6a4

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Theorems.Thm_ErdosRubinTaylor_dIn_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
namespace ErdosRubinTaylor
theorem _root_.solution (G : SimpleGraph V) (T : Set V) [Fintype T]
    [DecidableRel (G.induce T).Adj] (v : T) : (G.induce T).degree v = dIn G T v := by
  classical
  rw [dIn_eq, ← card_neighborFinset_eq_degree]
  refine card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [mem_neighborFinset, induce_adj] at ha
    simp [ha, a.2]
  · intro a _ b _ h; exact Subtype.ext h
  · intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩
end ErdosRubinTaylor
