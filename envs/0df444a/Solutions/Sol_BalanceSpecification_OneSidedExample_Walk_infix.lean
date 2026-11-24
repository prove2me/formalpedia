-- Prove2me | solution 1 for BalanceSpecification.OneSidedExample.Walk.infix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:47:53.649913+00:00
-- url     : https://prove2.me/submissions/2cdf7061-46fd-4847-b8ae-d6dff55db4ad

module
public import Definitions.Def_BalanceSpecificaton_OneSidedExample
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Theorems.Thm_BalanceSpecification_OneSidedExample_Walk_split

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.OneSidedExample
namespace BalanceSpecification.OneSidedExample
namespace Walk
theorem _root_.solution {s z : Vertex} {u v : Word Alphabet}
    (h : Walk s v z) (huv : u <:+: v) : ∃ t r, Walk t u r := by
  obtain ⟨p, q, rfl⟩ := huv
  obtain ⟨t, hpt, hq⟩ := h.split
  obtain ⟨r, _, hu⟩ := hpt.split
  exact ⟨r, t, hu⟩
end Walk
end BalanceSpecification.OneSidedExample
