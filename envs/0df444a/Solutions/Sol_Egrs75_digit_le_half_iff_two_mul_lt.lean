-- Prove2me | solution 1 for Egrs75.digit_le_half_iff_two_mul_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:26:31.815818+00:00
-- url     : https://prove2.me/submissions/9e72a0b5-0e05-431e-9f63-9f4a343ca307

module
public import Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Defs

set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat
namespace Egrs75
theorem _root_.solution {p d : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    d ≤ (p - 1) / 2 ↔ 2 * d < p := by
  obtain ⟨k, hk⟩ := hpodd
  -- p = 2k+1, so (p-1)/2 = k and the claim is `d ≤ k ↔ 2*d < 2k+1 ↔ 2*d ≤ 2k`.
  subst hk
  have hhalf : (2 * k + 1 - 1) / 2 = k := by
    have : 2 * k + 1 - 1 = 2 * k := by omega
    rw [this]; exact Nat.mul_div_cancel_left k (by decide)
  rw [hhalf]; omega
end Egrs75
