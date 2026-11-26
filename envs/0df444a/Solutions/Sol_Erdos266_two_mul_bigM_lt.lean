-- Prove2me | solution 1 for Erdos266.two_mul_bigM_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:44:07.629036+00:00
-- url     : https://prove2.me/submissions/50542cc6-0c40-43f9-9089-ea3e2e2640bc

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
public import Theorems.Thm_Erdos266_bigM_le_sqrt
public import Theorems.Thm_Erdos266_sixteen_le_bigN

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) : 2 * bigM k < bigN k := by
  have h16 := sixteen_le_bigN hk
  have hs : 4 ≤ Nat.sqrt (bigN k) := Nat.le_sqrt.mpr (by omega)
  have hM := bigM_le_sqrt k
  have h1 : 4 * Nat.sqrt (bigN k) ≤ Nat.sqrt (bigN k) * Nat.sqrt (bigN k) :=
    Nat.mul_le_mul_right _ hs
  have h2 : Nat.sqrt (bigN k) * Nat.sqrt (bigN k) ≤ bigN k := by
    have h := Nat.sqrt_le' (bigN k)
    rwa [pow_two] at h
  omega
end Erdos266
