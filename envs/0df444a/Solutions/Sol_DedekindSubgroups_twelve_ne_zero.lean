-- Prove2me | solution 1 for DedekindSubgroups.twelve_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:09:05.468648+00:00
-- url     : https://prove2.me/submissions/aaeaf152-73d9-424b-af0d-f9255a65069b

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p) : (12 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 12 := by
    have : ((12 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    exact (ZMod.natCast_eq_zero_iff _ _).mp this
  have hpr := hp.out
  rcases (Nat.Prime.dvd_mul hpr).mp (show p ∣ 4 * 3 from hdvd) with h4 | h3
  · rcases (Nat.Prime.dvd_mul hpr).mp (show p ∣ 2 * 2 from h4) with h2 | h2 <;>
      · have := Nat.le_of_dvd (by norm_num) h2; omega
  · have := Nat.le_of_dvd (by norm_num) h3; omega
end DedekindSubgroups
