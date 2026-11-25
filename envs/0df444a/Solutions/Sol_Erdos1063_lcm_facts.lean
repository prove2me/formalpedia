-- Prove2me | solution 1 for Erdos1063.lcm_facts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:35:28.417825+00:00
-- url     : https://prove2.me/submissions/7789fd87-e0c0-462d-9d9c-d5fec6bbccf7

module
public import Mathlib
public import Definitions.Def_Erdos1063_Lower

set_option autoImplicit false
@[expose] public section
public section
open Finset
open scoped Nat
open Erdos1063
namespace Erdos1063
theorem _root_.solution {k : ℕ} (hk : 3 ≤ k) :
    (Finset.Icc 1 (k - 1)).lcm id ≠ 0 ∧ 2 ≤ (Finset.Icc 1 (k - 1)).lcm id := by
  have hL0 : (Finset.Icc 1 (k - 1)).lcm id ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]; simp
  refine ⟨hL0, Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) ?_⟩
  have : (2:ℕ) ∈ Finset.Icc 1 (k - 1) := by simp; omega
  exact Finset.dvd_lcm this
end Erdos1063
