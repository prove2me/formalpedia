-- Prove2me | solution 1 for Erdos699.two_mul_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:49:14.489286+00:00
-- url     : https://prove2.me/submissions/f3bc6de9-dd5e-40ba-baa2-24f80b6ac1e4

module
public import Mathlib
public import Definitions.Def_Erdos699_Basic

set_option autoImplicit false
@[expose] public section
public section
open Erdos699
namespace Erdos699
theorem _root_.solution {s : Finset ℕ} {i : ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p < i) :
    2 * s.card ≤ i := by
  have h : s.card ≤ (Finset.range (i / 2)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p - 1) / 2) ?_ ?_
    · intro p hp
      have hp' : p ∈ s := by simpa using hp
      obtain ⟨hpp, hpi⟩ := hs p hp'
      have := hpp.two_le
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro p hp q hq hpq
      have hp' : p ∈ s := by simpa using hp
      have hq' : q ∈ s := by simpa using hq
      obtain ⟨hpp, -⟩ := hs p hp'
      obtain ⟨hqp, -⟩ := hs q hq'
      have h2p := hpp.two_le
      have h2q := hqp.two_le
      have hop := hpp.eq_two_or_odd
      have hoq := hqp.eq_two_or_odd
      simp only at hpq
      omega
  simp only [Finset.card_range] at h
  omega
end Erdos699
