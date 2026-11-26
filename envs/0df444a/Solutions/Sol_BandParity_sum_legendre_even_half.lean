-- Prove2me | solution 1 for BandParity.sum_legendre_even_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:42.804002+00:00
-- url     : https://prove2.me/submissions/5945e02c-7d18-4ec4-a1fa-438a76722a1d

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
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
theorem _root_.solution :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p ∧ v % 2 = 0), legendreSym p (v : ℤ) =
      legendreSym p 2 * kappa p := by
  unfold kappa
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun v => v / 2) (fun m => 2 * m) ?_ ?_ ?_ ?_ ?_
  · intro v hv; simp only [mem_filter, mem_range] at hv ⊢; omega
  · intro m hm; simp only [mem_filter, mem_range] at hm ⊢; omega
  · intro v hv; simp only [mem_filter, mem_range] at hv; omega
  · intro m _; simp
  · intro v hv
    simp only [mem_filter, mem_range] at hv
    rw [← legendreSym.mul]; congr 1; push_cast; omega
end BandParity
