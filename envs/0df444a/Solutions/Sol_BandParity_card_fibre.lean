-- Prove2me | solution 1 for BandParity.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:30.411957+00:00
-- url     : https://prove2.me/submissions/71c899b4-3095-4545-b438-b4f5a82f7508

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH
omit hN hN3 hH
namespace BandParity
theorem _root_.solution (x : (ZMod N)ˣ) (e : ℕ) {u₀ : (ZMod N)ˣ} (hu₀ : u₀ ∈ coset H x) :
    ((coset H x).filter (fun u => u ^ e = u₀ ^ e)).card = (powKer H e).card := by
  symm
  have hu' : x⁻¹ * u₀ ∈ H := by simpa [coset] using hu₀
  refine Finset.card_nbij' (fun k => u₀ * k) (fun u => u₀⁻¹ * u) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_coe, powKer, coset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hk ⊢
    refine ⟨by rw [← mul_assoc]; exact H.mul_mem hu' hk.1, by rw [mul_pow, hk.2, mul_one]⟩
  · intro u hu
    simp only [Finset.mem_coe, powKer, coset, Finset.mem_filter, Finset.mem_univ,
      true_and] at hu ⊢
    refine ⟨?_, by rw [mul_pow, inv_pow, hu.2, inv_mul_cancel]⟩
    have := H.mul_mem (H.inv_mem hu') hu.1
    rwa [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc x, mul_inv_cancel, one_mul] at this
  · intro k _; simp
  · intro u _; simp
end BandParity
