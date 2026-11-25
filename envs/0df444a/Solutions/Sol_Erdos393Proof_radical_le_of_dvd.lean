-- Prove2me | solution 1 for Erdos393Proof.radical_le_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:33:14.537684+00:00
-- url     : https://prove2.me/submissions/fc1bd122-fde7-4cba-81eb-f81ebeb12238

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
public import Theorems.Thm_Erdos393Proof_radical_pos

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution {m n : ℕ} (h : m ∣ n) (hn : n ≠ 0) : radical m ≤ radical n :=
  Nat.le_of_dvd (radical_pos n)
    (Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono h hn))
end Erdos393Proof
