-- Prove2me | solution 1 for BalanceSpecification.mem_language_constantShift_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:27.724781+00:00
-- url     : https://prove2.me/submissions/92d18979-f979-4d13-961f-2ff91016cf6b

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
public import Theorems.Thm_BalanceSpecification_block_constant

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}
namespace BalanceSpecification
theorem _root_.solution [TopologicalSpace A] [T1Space A]
    (a : A) {w : Word A} :
    w ∈ language (constantShift a) ↔ w = List.replicate w.length a := by
  constructor
  · rintro ⟨x, hx, k, hk⟩
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact hk.symm.trans (block_constant a k w.length)
  · intro hw
    refine ⟨fun _ => a, Set.mem_singleton _, 0, ?_⟩
    exact (block_constant a 0 w.length).trans hw.symm
end BalanceSpecification
