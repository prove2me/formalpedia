-- Prove2me | solution 1 for Erdos287.adjacent_pair_prices_combine_local_pattern_bounds
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T16:17:23.118623+00:00
-- url     : https://prove2.me/submissions/ab6162d7-0a29-4056-b3e1-dba9c3cec8b6

import Mathlib

open Finset

set_option autoImplicit false

private def pairWeight {R : Type} [AddCommMonoid R] (price : ℕ → R) (e n : ℕ) : R :=
  (if n = e then price e else 0) + (if n = e + 1 then price e else 0)

private theorem edge_price_le {R : Type} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (D : Finset ℕ) (price : ℕ → R) (e : ℕ)
    (hnonneg : 0 ≤ price e) (hcover : e ∈ D ∨ e + 1 ∈ D) :
    price e ≤ ∑ n ∈ D, pairWeight price e n := by
  simp only [pairWeight, sum_add_distrib, sum_ite_eq']
  rcases hcover with h | h
  · simp only [h, if_true]
    split_ifs
    · exact le_add_of_nonneg_right hnonneg
    · rw [add_zero]
  · simp only [h, if_true]
    split_ifs
    · exact le_add_of_nonneg_left hnonneg
    · rw [zero_add]

/-- Upper bounds on separate residue tables can be added with prices for
adjacent pairs. Local weights vanish outside their blocks. -/
theorem solution {ι R : Type} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (G : Finset ι) (D E : Finset ℕ)
    (w price : ℕ → R) (localWeight : ι → ℕ → R) (upper : ι → R)
    (hprice : ∀ e ∈ E, 0 ≤ price e)
    (hcover : ∀ e ∈ E, e ∈ D ∨ e + 1 ∈ D)
    (hweight : ∀ n ∈ D, (∑ j ∈ G, localWeight j n) = w n +
      ∑ e ∈ E, ((if n = e then price e else 0) + (if n = e + 1 then price e else 0)))
    (hupper : ∀ j ∈ G, (∑ n ∈ D, localWeight j n) ≤ upper j) :
    (∑ n ∈ D, w n) + (∑ e ∈ E, price e) ≤ ∑ j ∈ G, upper j := by
  have hprices : (∑ e ∈ E, price e) ≤ ∑ e ∈ E, ∑ n ∈ D, pairWeight price e n :=
    sum_le_sum fun e he => edge_price_le D price e (hprice e he) (hcover e he)
  have htranspose : (∑ e ∈ E, ∑ n ∈ D, pairWeight price e n) =
      ∑ n ∈ D, ∑ e ∈ E, pairWeight price e n := sum_comm
  have hmerge : (∑ n ∈ D, (w n + ∑ e ∈ E, pairWeight price e n)) =
      (∑ n ∈ D, w n) + (∑ n ∈ D, ∑ e ∈ E, pairWeight price e n) := sum_add_distrib
  have hbalance : (∑ n ∈ D, (w n + ∑ e ∈ E, pairWeight price e n)) =
      ∑ n ∈ D, ∑ j ∈ G, localWeight j n :=
    sum_congr rfl fun n hn => (hweight n hn).symm
  have hblocks : (∑ n ∈ D, ∑ j ∈ G, localWeight j n) =
      ∑ j ∈ G, ∑ n ∈ D, localWeight j n := sum_comm
  have hbound : (∑ j ∈ G, ∑ n ∈ D, localWeight j n) ≤ ∑ j ∈ G, upper j :=
    sum_le_sum hupper
  calc
    _ ≤ (∑ n ∈ D, w n) + (∑ e ∈ E, ∑ n ∈ D, pairWeight price e n) :=
      add_le_add (le_refl _) hprices
    _ = (∑ n ∈ D, w n) + (∑ n ∈ D, ∑ e ∈ E, pairWeight price e n) :=
      congrArg (fun r : R => (∑ n ∈ D, w n) + r) htranspose
    _ = ∑ n ∈ D, (w n + ∑ e ∈ E, pairWeight price e n) := hmerge.symm
    _ = ∑ n ∈ D, ∑ j ∈ G, localWeight j n := hbalance
    _ = ∑ j ∈ G, ∑ n ∈ D, localWeight j n := hblocks
    _ ≤ _ := hbound

