-- Prove2me | solution 1 for CliqueMinors.DiracCtx.card_nbr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:40:18.462836+00:00
-- url     : https://prove2.me/submissions/d4e91489-90a8-4497-8bd4-679a383be51e

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_P2M_CliqueMinors_DiracCtx_deg__09077c9cb2b4

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
open CliqueMinors.DiracCtx
variable {G : SimpleGraph V} {S : Finset V}
namespace CliqueMinors.DiracCtx
theorem _root_.solution (H : DiracCtx G S) {v w : V} (h : G.Adj v w) :
    3 ≤ (G.neighborFinset v).card := by
  rw [card_neighborFinset_eq_degree]; exact H.deg' h
end CliqueMinors.DiracCtx
