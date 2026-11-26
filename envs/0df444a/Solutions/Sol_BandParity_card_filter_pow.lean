-- Prove2me | solution 1 for BandParity.card_filter_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:59:06.646101+00:00
-- url     : https://prove2.me/submissions/454a9383-1539-442f-9f90-21ca76da2276

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup
public import Theorems.Thm_BandParity_card_fibre

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
theorem _root_.solution (x : (ZMod N)ˣ) (e : ℕ) (P : (ZMod N)ˣ → Prop) [DecidablePred P] :
    ((coset H x).filter (fun u => P (u ^ e))).card =
      (powKer H e).card * (((coset H x).image (· ^ e)).filter P).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := (· ^ e))
    (t := ((coset H x).image (· ^ e)).filter P)
    (fun u hu => by
      simp only [Finset.mem_coe, Finset.mem_filter] at hu ⊢
      exact ⟨Finset.mem_image_of_mem _ hu.1, hu.2⟩)]
  rw [Finset.sum_congr rfl (g := fun _ => (powKer H e).card), Finset.sum_const, smul_eq_mul,
    mul_comm]
  intro y hy
  simp only [mem_filter, mem_image] at hy
  obtain ⟨⟨u₀, hu₀, rfl⟩, hP⟩ := hy
  rw [← card_fibre x e hu₀, Finset.filter_filter]
  congr 1; ext u
  simp only [mem_filter]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, by rw [h3]; exact hP, h3⟩
end BandParity
