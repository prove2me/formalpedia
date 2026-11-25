-- Prove2me | solution 1 for Erdos393Proof.radical_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:33:17.449031+00:00
-- url     : https://prove2.me/submissions/30ce2085-3739-470d-ab8d-965f17d6e9ef

module
public import Mathlib
public import Definitions.Def_Erdos393Palomar_Solution
public import Theorems.Thm_Erdos393Proof_radical_eq
public import Theorems.Thm_Erdos393Proof_radical_pos
public import Theorems.Thm_Erdos393Proof_radical_zero

set_option autoImplicit true
@[expose] public section
public section
open Filter Asymptotics
open scoped Nat
open Erdos393Proof
open ABC Polynomial
namespace Erdos393Proof
theorem _root_.solution (a b : ℕ) : radical (a * b) ≤ radical a * radical b := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [zero_mul, radical_zero, one_mul]; exact radical_pos b
  rcases eq_or_ne b 0 with rfl | hb
  · rw [mul_zero, radical_zero, mul_one]; exact radical_pos a
  refine Nat.le_of_dvd (Nat.mul_pos (radical_pos a) (radical_pos b)) ?_
  rw [radical_eq, radical_eq, radical_eq, Nat.primeFactors_mul ha hb, ← Finset.prod_union_inter]
  exact dvd_mul_right _ _
end Erdos393Proof
