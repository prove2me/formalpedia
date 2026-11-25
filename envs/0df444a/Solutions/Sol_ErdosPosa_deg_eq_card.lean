-- Prove2me | solution 1 for ErdosPosa.deg_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:22:31.944617+00:00
-- url     : https://prove2.me/submissions/4219b364-3bb9-492d-b1df-2e0e6d8b1ff7

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}
namespace ErdosPosa
theorem _root_.solution [Fintype V] [DecidableRel H.Adj] (x : V) :
    deg H x = (Finset.univ.filter (fun y => H.Adj x y)).card := by
  rw [deg, ← Set.ncard_coe_finset]
  congr 1
  ext y; simp
end ErdosPosa
