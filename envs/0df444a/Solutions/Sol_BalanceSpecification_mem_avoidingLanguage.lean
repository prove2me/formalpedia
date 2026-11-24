-- Prove2me | solution 1 for BalanceSpecification.mem_avoidingLanguage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:32:11.306842+00:00
-- url     : https://prove2.me/submissions/534c6a27-61cf-4488-bf5d-1da9bee21e96

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
omit [Fintype A]
namespace BalanceSpecification
theorem _root_.solution {v w : Word A} :
    w ∈ avoidingLanguage L v ↔ w ∈ L ∧ ¬v <:+: w := Iff.rfl
end BalanceSpecification
