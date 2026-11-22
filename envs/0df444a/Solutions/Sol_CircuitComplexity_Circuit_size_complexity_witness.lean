-- Prove2me | solution 1 for CircuitComplexity.Circuit.size_complexity_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:10:09.078191+00:00
-- url     : https://prove2.me/submissions/b1103776-7702-4134-a40d-e647fb1fcd59

module
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth
section
@[expose] public section
namespace CircuitComplexity
namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]
end Circuit
namespace Circuit
variable {B : Basis} {N : Nat} [NeZero N]
private theorem size_complexity_set_nonempty [CompleteBasis B]
    (f : BitString N → Bool) :
    {s | ∃ G, ∃ c : Circuit B N 1 G, c.size = s ∧ (fun x => (c.eval x) 0) = f}.Nonempty := by
  obtain ⟨G, c, hc⟩ := CompleteBasis.complete (B := B) (fun x => (fun _ : Fin 1 => f x))
  refine ⟨c.size, G, c, rfl, ?_⟩
  simp_all
end Circuit
end CircuitComplexity
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Circuit
variable {B : Basis} {N : Nat} [NeZero N]
namespace CircuitComplexity.Circuit
theorem _root_.solution [CompleteBasis B]
    (f : BitString N → Bool) :
    ∃ G, ∃ c : Circuit B N 1 G,
      c.size = sizeComplexity B f ∧ (fun x => (c.eval x) 0) = f :=
  Nat.sInf_mem (size_complexity_set_nonempty (B := B) f)
end CircuitComplexity.Circuit
