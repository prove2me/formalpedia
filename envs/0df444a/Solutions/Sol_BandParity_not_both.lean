-- Prove2me | solution 1 for BandParity.not_both
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:01.764996+00:00
-- url     : https://prove2.me/submissions/8d023350-29c7-4a25-b817-8f7ddea73ee8

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup
public import Theorems.Thm_BandParity_neg_one_not_mem

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
omit [NeZero N] hN [DecidablePred (· ∈ H)]
namespace BandParity
theorem _root_.solution (x u : (ZMod N)ˣ) : ¬ (x⁻¹ * u ∈ H ∧ -(x⁻¹ * u) ∈ H) := by
  rintro ⟨h1, h2⟩
  apply neg_one_not_mem hN3 hH
  have := H.mul_mem (H.inv_mem h1) h2
  rwa [mul_neg, inv_mul_cancel] at this
end BandParity
