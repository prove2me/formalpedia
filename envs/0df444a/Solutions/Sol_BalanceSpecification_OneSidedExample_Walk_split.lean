-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:48:31.878121+00:00
-- url     : https://prove2.me/submissions/f0d5e8ad-3f06-4ecd-88f1-9a19346e7849

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
theorem _root_.solution {s z : Vertex} {u v : Word Alphabet}
    (h : Walk s (u ++ v) z) : ∃ t, Walk s u t ∧ Walk t v z := by
  induction u generalizing s with
  | nil => exact ⟨s, .nil s, h⟩
  | cons d u ih =>
    cases h with
    | cons he hw =>
      obtain ⟨t, hu, hv⟩ := ih hw
      exact ⟨t, .cons he hu, hv⟩
end Walk
end BalanceSpecification.OneSidedExample
