-- Prove2me | solution 1 for BalanceSpecification.isConcatenation_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:21:03.175725+00:00
-- url     : https://prove2.me/submissions/d16b4972-7f7b-46c9-8ae2-4cd13488ac3b

module
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Topology.Continuous
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Coded

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}
namespace BalanceSpecification
theorem _root_.solution {C D : Set (Word A)} (hCD : C ⊆ D)
    {x : Configuration A} (hx : IsConcatenation C x) : IsConcatenation D x := by
  obtain ⟨p, hp, hwords⟩ := hx
  exact ⟨p, hp, fun i => hCD (hwords i)⟩
end BalanceSpecification
