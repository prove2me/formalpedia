-- Prove2me | solution 1 for BalanceSpecification.mem_codedShift_of_isConcatenation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:30.552002+00:00
-- url     : https://prove2.me/submissions/4cd84c49-33b4-44ef-b3af-f0d2a66c0fdd

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
theorem _root_.solution [TopologicalSpace A]
    {C : Set (Word A)} {x : Configuration A} (hx : IsConcatenation C x) :
    x ∈ (codedShift C).carrier := subset_closure hx
end BalanceSpecification
