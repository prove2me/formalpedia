-- Prove2me | solution 1 for Erdos699.le_sq_of_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:59:44.506055+00:00
-- url     : https://prove2.me/submissions/7b306694-dee4-4f39-b553-c7e159184ecb

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic
public import Theorems.Thm_Erdos699_choose_mul_pow_le
public import Theorems.Thm_Erdos699_choose_dvd_gcd_mul
public import Theorems.Thm_Erdos699_le_pow_card_of_dvd_choose
public import Theorems.Thm_Erdos699_two_mul_card_le

set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
theorem _root_.solution {n i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hjn : j ≤ n / 2)
    (hcon : ∀ p : ℕ, p.Prime → i ≤ p → ¬ p ∣ Nat.gcd (n.choose i) (n.choose j)) :
    n ≤ j ^ 2 := by
  have hjn' : j ≤ n := le_trans hjn (Nat.div_le_self n 2)
  have hin : i ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hA : 0 < n.choose i := Nat.choose_pos hin
  have hB : 0 < j.choose i := Nat.choose_pos hij.le
  set g := Nat.gcd (n.choose i) (n.choose j) with hg_def
  have hg0 : g ≠ 0 := (Nat.gcd_pos_of_pos_left _ hA).ne'
  -- `C(n, i) ≤ g · C(j, i)`
  have h1 : n.choose i ≤ g * j.choose i :=
    Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero hg0) hB) (choose_dvd_gcd_mul hij.le)
  -- `g ≤ n ^ c` with `2c ≤ i`, since every prime factor of `g` is below `i`
  have h3 : g ≤ n ^ g.primeFactors.card :=
    le_pow_card_of_dvd_choose hn0 hg0 hin (Nat.gcd_dvd_left _ _)
  have hc : 2 * g.primeFactors.card ≤ i := by
    refine two_mul_card_le (fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩)
    by_contra hpi
    exact hcon p (Nat.prime_of_mem_primeFactors hp) (not_lt.1 hpi)
      (Nat.dvd_of_mem_primeFactors hp)
  set c := g.primeFactors.card
  -- `C(j, i) · n^i ≤ C(n, i) · j^i`
  have h2 := choose_mul_pow_le (i := i) hjn'
  have h4 : j.choose i * n ^ i ≤ j.choose i * (n ^ c * j ^ i) :=
    calc j.choose i * n ^ i ≤ n.choose i * j ^ i := h2
      _ ≤ g * j.choose i * j ^ i := Nat.mul_le_mul_right _ h1
      _ ≤ n ^ c * j.choose i * j ^ i := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h3)
      _ = j.choose i * (n ^ c * j ^ i) := by ring
  have h5 : n ^ i ≤ n ^ c * j ^ i := Nat.le_of_mul_le_mul_left h4 hB
  have h6 : n ^ i * n ^ i ≤ n ^ i * (j ^ 2) ^ i :=
    calc n ^ i * n ^ i ≤ (n ^ c * j ^ i) * (n ^ c * j ^ i) := Nat.mul_le_mul h5 h5
      _ = n ^ (2 * c) * (j ^ 2) ^ i := by ring
      _ ≤ n ^ i * (j ^ 2) ^ i := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hnpos hc)
  have h7 : n ^ i ≤ (j ^ 2) ^ i := Nat.le_of_mul_le_mul_left h6 (Nat.pow_pos hnpos)
  exact (Nat.pow_le_pow_iff_left (by omega)).1 h7
end Erdos699
