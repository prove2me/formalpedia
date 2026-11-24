-- Prove2me | solution 1 for FFactor.even_sum_card_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:53:29.800022+00:00
-- url     : https://prove2.me/submissions/7541a714-c333-4a9e-b3fa-b66056c2006d

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace FFactor
theorem _root_.solution (H : SimpleGraph V) [DecidableRel H.Adj] (s : Finset V) :
    Even (∑ w ∈ s, #{u ∈ s | H.Adj w u}) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    have h1 : #{u ∈ insert a s | H.Adj a u} = #{u ∈ s | H.Adj a u} := by
      rw [filter_insert, if_neg (H.loopless.irrefl a)]
    have h2 : ∀ w ∈ s, #{u ∈ insert a s | H.Adj w u} =
        #{u ∈ s | H.Adj w u} + if H.Adj w a then 1 else 0 := by
      intro w hw
      rw [filter_insert]
      split_ifs with h
      · rw [card_insert_of_notMem (by simp [ha])]
      · simp
    rw [sum_congr rfl h2, sum_add_distrib, ← card_filter]
    have h3 : #{w ∈ s | H.Adj w a} = #{u ∈ s | H.Adj a u} := by
      congr 1; ext; simp [H.adj_comm]
    rw [h1, h3]
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + #{u ∈ s | H.Adj a u}, by omega⟩
end FFactor
