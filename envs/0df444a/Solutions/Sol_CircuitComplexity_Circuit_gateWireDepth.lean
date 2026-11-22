-- Prove2me | solution 1 for CircuitComplexity.Circuit.gateWireDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:09.045809+00:00
-- url     : https://prove2.me/submissions/bdc93a7f-fcf2-4dc6-b5a0-0be3d1fa3c8e

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.Circuit
theorem _root_.solution (c : Circuit B N M G)
    (w : Fin (N + G)) (h : ¬ (w.val < N)) :
    c.wireDepth w =
      1 + Fin.foldl (c.gates ⟨w.val - N, by omega⟩).fanIn
        (fun acc k => max acc (c.wireDepth ((c.gates ⟨w.val - N, by omega⟩).inputs k))) 0 := by
  conv_lhs => unfold wireDepth
  simp only [h, dite_false]
end CircuitComplexity.Circuit
