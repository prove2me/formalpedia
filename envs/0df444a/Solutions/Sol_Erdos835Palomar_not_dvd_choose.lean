-- Prove2me | solution 1 for Erdos835Palomar.not_dvd_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:12:26.881357+00:00
-- url     : https://prove2.me/submissions/e0d550ae-ec4a-4d28-908a-70e56e1adda8

module
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib
public import Definitions.Def_Erdos835Palomar_Solution

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open Erdos835Palomar
namespace Erdos835Palomar
theorem _root_.solution (k p : ℕ) (hp : p.Prime) (hpk : p ∣ k + 1) (hlt : p < k + 1) :
    ¬ (k + 1) ∣ (k + p).choose p := by
  rintro ⟨t, ht⟩
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have hA : (k + 1).ascFactorial (q + 1) =
      (q + 1).factorial * (k + (q + 1)).choose (q + 1) :=
    Nat.ascFactorial_eq_factorial_mul_choose k (q + 1)
  rw [Nat.ascFactorial_eq_prod_range, Finset.prod_range_succ', ht, add_zero] at hA
  have hQ : (∏ i ∈ range q, (k + 1 + (i + 1))) = (q + 1).factorial * t := by
    have h2 : (∏ i ∈ range q, (k + 1 + (i + 1))) * (k + 1) =
        ((q + 1).factorial * t) * (k + 1) := by
      rw [hA]; ring
    exact Nat.eq_of_mul_eq_mul_right (by omega) h2
  have hdvd : q + 1 ∣ ∏ i ∈ range q, (k + 1 + (i + 1)) := by
    rw [hQ]; exact Dvd.dvd.mul_right (Nat.dvd_factorial (by omega) le_rfl) t
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd
  have h3 : q + 1 ∣ i + 1 := (Nat.dvd_add_right hpk).mp hdi
  have h4 := Finset.mem_range.mp hi
  have h5 := Nat.le_of_dvd (by omega) h3
  omega
end Erdos835Palomar
