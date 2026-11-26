-- Prove2me | solution 1 for BandParity.card_coset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:56:29.820886+00:00
-- url     : https://prove2.me/submissions/c9c70335-fe43-4a58-9dcd-71387fb4172c

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
theorem _root_.solution (x : (ZMod N)ˣ) : (coset H x).card = Nat.card H := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  refine Finset.card_nbij' (fun u => x⁻¹ * u) (fun k => x * k) ?_ ?_ ?_ ?_
  · intro u hu; simpa [coset] using hu
  · intro k hk; simpa [coset] using hk
  · intro u _; simp
  · intro k _; simp
end BandParity
