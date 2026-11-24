-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.edge_selected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:48:41.609734+00:00
-- url     : https://prove2.me/submissions/9186cf88-19b9-4393-bca1-f7fccb105542

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
theorem _root_.solution (s : Vertex) (d : Bool) : Edge s (edgeLabel s d) (edgeTarget s d) := by
  cases s with
  | q n => cases d; exact .qa n; exact .qb n
  | p n => cases n with
    | zero => cases d; exact .pa; exact .pc 0
    | succ n => cases d; exact .pb n; exact .pc (n + 1)
end BalanceSpecification.OneSidedExample
