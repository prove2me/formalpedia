-- Prove2me | solution 1 for CircuitComplexity.Circuit.inputWireDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:08:58.503814+00:00
-- url     : https://prove2.me/submissions/e9b225ac-d789-42b3-8835-6e5845a2b6f4

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
namespace CircuitComplexity.Circuit
theorem _root_.solution (c : Circuit B N M G)
    (w : Fin (N + G)) (h : w.val < N) :
    c.wireDepth w = 0 := by
  unfold wireDepth; simp [h]
end CircuitComplexity.Circuit
