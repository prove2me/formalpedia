-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:40:17.926443+00:00
-- url     : https://prove2.me/submissions/94e679cc-1233-4c0c-a6f1-f3f75d815c0d

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
namespace Walk
theorem _root_.solution {s t z : Vertex} {u v : Word Alphabet}
    (hu : Walk s u t) (hv : Walk t v z) : Walk s (u ++ v) z := by
  induction hu with
  | nil => exact hv
  | cons he hu ih => exact .cons he (ih hv)
end Walk
end BalanceSpecification.OneSidedExample
