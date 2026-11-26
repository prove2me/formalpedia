-- Prove2me | solution 1 for BandParity.sum_alt_legendre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:11:28.101957+00:00
-- url     : https://prove2.me/submissions/802e7a19-c2e2-4c14-8ef3-f3e84b6f4d5d

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_sum_legendre_half
public import Theorems.Thm_BandParity_sum_legendre_even_half
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp8 : p % 8 = 5) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), (-1 : ℤ) ^ v * legendreSym p (v : ℤ) =
      -2 * kappa p := by
  have hp2 : p ≠ 2 := by omega
  have h2 : legendreSym p 2 = -1 := by
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_mod_eight, hp8]; decide
  have hsplit : ∀ v : ℕ, (-1 : ℤ) ^ v * legendreSym p (v : ℤ) =
      2 * (if v % 2 = 0 then legendreSym p (v : ℤ) else 0) - legendreSym p (v : ℤ) := by
    intro v
    rcases Nat.even_or_odd v with he | ho
    · rw [he.neg_one_pow]
      split_ifs with hh
      · ring
      · exact absurd (Nat.even_iff.1 he) hh
    · have : v % 2 ≠ 0 := by rw [Nat.odd_iff] at ho; omega
      rw [ho.neg_one_pow]
      split_ifs with hh
      · exact absurd hh this
      · ring
  rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_filter, Finset.filter_filter, sum_legendre_half (by omega)]
  have : (range p).filter (fun v => (0 < v ∧ 2 * v < p) ∧ v % 2 = 0) =
      (range p).filter (fun v => 0 < v ∧ 2 * v < p ∧ v % 2 = 0) := by
    ext v; simp only [mem_filter]; tauto
  rw [this, sum_legendre_even_half, h2]; ring
end BandParity
