-- Prove2me | solution 1 for CircuitComplexity.Circuit.exists_gate_reads_input
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:14:07.758809+00:00
-- url     : https://prove2.me/submissions/a864979e-7374-4587-88e4-aaa8ba05eac1

module
public import Definitions.Def_LeanPool_CircuitComplexity_EssentialInput
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Sum
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_LowerBound
public import Theorems.Thm_CircuitComplexity_Circuit_eval_eq_of_unreferenced

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.Circuit
theorem _root_.solution
    (c : Circuit B N M G) (f : BitString N → BitString M)
    (hf : c.eval = f) (i : Fin N) (hdep : IsEssentialInput f i) :
    (∃ g : Fin G, ∃ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val = i.val) ∨
    (∃ j : Fin M, ∃ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val = i.val) := by
  by_contra h
  push Not at h
  obtain ⟨hg, ho⟩ := h
  obtain ⟨x, hx⟩ := hdep
  exact hx (hf ▸ eval_eq_of_unreferenced c i _ hg ho x)
end CircuitComplexity.Circuit
