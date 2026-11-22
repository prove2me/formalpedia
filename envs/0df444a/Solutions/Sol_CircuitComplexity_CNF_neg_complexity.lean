-- Prove2me | solution 1 for CircuitComplexity.CNF.neg_complexity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:06.382813+00:00
-- url     : https://prove2.me/submissions/10677f90-d5e3-4689-93dd-3634cbf1988b

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
namespace CNF
theorem _root_.solution (φ : CNF N) : φ.neg.complexity = φ.complexity := by
  simp [CNF.neg, DNF.complexity, CNF.complexity, List.length_map]
end CNF
end CircuitComplexity
