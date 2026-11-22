-- Prove2me | solution 1 for CircuitComplexity.Literal.eval_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:13.54497+00:00
-- url     : https://prove2.me/submissions/2c2ce06f-2f90-44aa-8cd7-bc1e119f0fad

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace Literal
theorem _root_.solution (l : Literal N) (x : BitString N) :
    l.neg.eval x = !(l.eval x) := by
  obtain ⟨v, p⟩ := l
  simp only [Literal.neg, Literal.eval]
  cases p <;> simp
end Literal
end CircuitComplexity
