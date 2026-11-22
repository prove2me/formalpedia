-- Prove2me | solution 1 for CircuitComplexity.Schnorr.xorBool_essential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:11.525961+00:00
-- url     : https://prove2.me/submissions/bfe4e73d-28ae-4fb3-ae28-e57264fb5ec5

module
public import Definitions.Def_LeanPool_CircuitComplexity_Basic
public import Definitions.Def_LeanPool_CircuitComplexity_XOR
public import Theorems.Thm_CircuitComplexity_Schnorr_xorBool_flip
public import Theorems.Thm_CircuitComplexity_Circuit_inputWireDepth
attribute [local simp] CircuitComplexity.Circuit.inputWireDepth



set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity
open CircuitComplexity.Schnorr
namespace CircuitComplexity.Schnorr
theorem _root_.solution (N : Nat) (a : Fin N) (x : BitString N) :
    xorBool N x ≠ xorBool N (Function.update x a (!x a)) := by
  rw [xorBool_flip]; cases xorBool N x <;> simp
end CircuitComplexity.Schnorr
