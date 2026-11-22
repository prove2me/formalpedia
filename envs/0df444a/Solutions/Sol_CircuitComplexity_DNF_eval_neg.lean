-- Prove2me | solution 1 for CircuitComplexity.DNF.eval_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:11:34.484036+00:00
-- url     : https://prove2.me/submissions/03661528-501e-484e-9fe0-07dbd09b5f5a

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Theorems.Thm_CircuitComplexity_Literal_eval_neg
public import Theorems.Thm_CircuitComplexity_CNF_eval_neg
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
namespace CircuitComplexity
namespace DNF
theorem _root_.solution (φ : DNF N) (x : BitString N) :
    φ.neg.eval x = !(φ.eval x) := by
  simp only [DNF.neg, CNF.eval, DNF.eval, List.any_map, List.all_map, Function.comp_def,
    List.not_all_eq_any_not, List.not_any_eq_all_not, Literal.eval_neg]
end DNF
end CircuitComplexity
