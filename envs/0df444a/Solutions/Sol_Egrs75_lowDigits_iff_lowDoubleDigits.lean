-- Prove2me | solution 1 for Egrs75.lowDigits_iff_lowDoubleDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T17:29:50.873733+00:00
-- url     : https://prove2.me/submissions/4fb96fbb-7605-4bf7-aff9-7ca67edbe26f

module
public import Definitions.Def_LeanPool_Egrs75_CentralBinomialDigits
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Theorems.Thm_Egrs75_digit_le_half_iff_two_mul_lt

set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat
namespace Egrs75
theorem _root_.solution {p n : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) :
    LowDigits p n ↔ Egrs75.Erdos376.LowDoubleDigits p n := by
  unfold LowDigits Egrs75.Erdos376.LowDoubleDigits
  constructor
  · intro h d hd; exact (digit_le_half_iff_two_mul_lt hp2 hpodd).mp (h d hd)
  · intro h d hd; exact (digit_le_half_iff_two_mul_lt hp2 hpodd).mpr (h d hd)
end Egrs75
