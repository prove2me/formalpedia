-- Prove2me | solution 1 for Expanders.sum_neighbor_swap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:29:20.047869+00:00
-- url     : https://prove2.me/submissions/d67e1e98-33e7-4bf0-9b4a-4b5211aba296

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] (F : V → V → ℝ) :
    ∑ v, ∑ w ∈ G.neighborFinset v, F v w = ∑ v, ∑ w ∈ G.neighborFinset v, F w v := by
  have key : ∀ (H : V → V → ℝ) v, ∑ w ∈ G.neighborFinset v, H v w =
      ∑ w, if G.Adj v w then H v w else 0 := by
    intro H v
    rw [← Finset.sum_filter]; congr 1; ext w; simp
  rw [Finset.sum_congr rfl (fun v _ => key F v),
    Finset.sum_congr rfl (fun v _ => key (fun a b => F b a) v), Finset.sum_comm]
  simp_rw [G.adj_comm]
end Expanders
