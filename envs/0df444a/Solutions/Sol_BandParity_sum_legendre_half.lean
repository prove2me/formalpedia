-- Prove2me | solution 1 for BandParity.sum_legendre_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:09:03.557915+00:00
-- url     : https://prove2.me/submissions/ad3546c7-19a0-48e1-af20-e2365e05e7fe

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
public import Theorems.Thm_BandParity_ringChar_ne_two
public import Theorems.Thm_BandParity_quadraticChar_neg
public import Theorems.Thm_BandParity_quadraticChar_eq_legendreSym
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
public import Theorems.Thm_BandParity_sum_eq_two_nsmul_half
public import Theorems.Thm_BandParity_sum_filter_val
public import Theorems.Thm_P2M_BandParity_sum_half_eq_sum_half__95af2de0d67d
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace BandParity
theorem _root_.solution (hp4 : p % 4 = 1) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), legendreSym p (v : ℤ) = 0 := by
  have hp2 : p ≠ 2 := by omega
  have h := sum_eq_two_nsmul_half hp2 (fun x => quadraticChar (ZMod p) x)
    (quadraticChar_zero) (quadraticChar_neg hp4)
  rw [quadraticChar_sum_zero (ringChar_ne_two hp2),
    sum_half_eq_sum_half' _ quadraticChar_zero] at h
  simp only [quadraticChar_eq_legendreSym] at h
  rw [sum_filter_val (fun v => 0 < v ∧ 2 * v < p) (fun v => legendreSym p (v : ℤ)),
    two_nsmul] at h
  omega
end BandParity
