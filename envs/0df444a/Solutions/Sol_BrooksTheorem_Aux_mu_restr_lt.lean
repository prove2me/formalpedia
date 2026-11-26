-- Prove2me | solution 1 for BrooksTheorem.Aux.mu_restr_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:36:22.387375+00:00
-- url     : https://prove2.me/submissions/04b2b0fc-6224-4e40-ae59-9f6632c6f6fa

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
public import Theorems.Thm_BrooksTheorem_Aux_mem_pairs

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (H : SimpleGraph V) (S : Set V) {u v : V} (h : H.Adj u v) (hu : u ∉ S) :
    mu (restr H S) < mu H := by
  apply card_lt_card
  refine ⟨fun p hp => mem_pairs.2 (mem_pairs.1 hp).1, fun hsub => ?_⟩
  have := mem_pairs.1 (hsub (mem_pairs.2 (show H.Adj (u, v).1 (u, v).2 from h)))
  exact hu this.2.1
end BrooksTheorem.Aux
