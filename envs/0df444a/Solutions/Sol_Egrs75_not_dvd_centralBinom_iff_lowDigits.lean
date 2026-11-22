-- Prove2me | solution 1 for Egrs75.not_dvd_centralBinom_iff_lowDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:30:28.044848+00:00
-- url     : https://prove2.me/submissions/c97dd8b4-0385-401b-8dd6-91703c9767e7

module
public import Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Theorems.Thm_Egrs75_lowDigits_iff_lowDoubleDigits

set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat
namespace Egrs75
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (n : ℕ) : ¬ p ∣ Nat.centralBinom n ↔ LowDigits p n := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcop := Egrs75.Erdos376.coprime_centralBinom_prime_iff (p := p) n
  -- `Coprime (centralBinom n) p ↔ ¬ p ∣ centralBinom n`
  have hnotdvd : Nat.Coprime (Nat.centralBinom n) p ↔ ¬ p ∣ Nat.centralBinom n := by
    rw [Nat.coprime_comm]; exact hp.coprime_iff_not_dvd
  rw [← hnotdvd, hcop, ← lowDigits_iff_lowDoubleDigits hp2 hpodd]
end Egrs75
