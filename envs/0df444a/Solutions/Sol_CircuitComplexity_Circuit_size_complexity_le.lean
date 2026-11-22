-- Prove2me | solution 1 for CircuitComplexity.Circuit.size_complexity_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:09:24.447893+00:00
-- url     : https://prove2.me/submissions/99b256b8-e721-4cd5-9bb0-bedfccdf7b85

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N : Nat} [NeZero N]
namespace CircuitComplexity.Circuit
theorem _root_.solution {G : Nat}
    (c : Circuit B N 1 G) (f : BitString N → Bool)
    (hf : (fun x => (c.eval x) 0) = f) :
    sizeComplexity B f ≤ c.size :=
  Nat.sInf_le ⟨G, c, rfl, hf⟩
end CircuitComplexity.Circuit
