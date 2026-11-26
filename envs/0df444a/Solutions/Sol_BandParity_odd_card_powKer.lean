-- Prove2me | solution 1 for BandParity.odd_card_powKer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:57:25.126539+00:00
-- url     : https://prove2.me/submissions/a8d00fdd-b1c8-4fde-96aa-bca49c9c321b

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
omit hN hN3
namespace BandParity
theorem _root_.solution (e : ℕ) : Odd (powKer H e).card := by
  classical
  let K : Subgroup (ZMod N)ˣ := H ⊓ (powMonoidHom e).ker
  have hK : (powKer H e).card = Nat.card K := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1; ext k
    simp [powKer, K, Subgroup.mem_inf, MonoidHom.mem_ker]
  have hdvd : Nat.card K ∣ Nat.card H := Subgroup.card_dvd_of_le inf_le_left
  rw [hK]
  exact Odd.of_dvd_nat hH hdvd
end BandParity
