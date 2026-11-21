-- Prove2me | solution 1 for Champernowne.getElemOption_bigDigits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:40:38.955433+00:00
-- url     : https://prove2.me/submissions/0e197d28-f039-4552-a79a-c24de98c1643

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Mathlib.Data.List.GetD
public import Definitions.Def_LeanPool_Champernowne_CountExtras

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b m n : ℕ} (hb : 1 < b)
    (hlen : (bigDigits b n).length = m) {j : ℕ} (hj : j < m) :
    (bigDigits b n)[j]? = some (n / b ^ (m - 1 - j) % b) := by
  have hlen' : (Nat.digits b n).length = m := by
    simpa [bigDigits] using hlen
  change (Nat.digits b n).reverse[j]? = _
  rw [List.getElem?_reverse (by omega), hlen',
    List.getElem?_eq_getElem (by omega)]
  have hgd := Nat.getD_digits n (m - 1 - j) (show 2 ≤ b from hb)
  rw [List.getD_eq_getElem _ _ (by omega)] at hgd
  exact congrArg some hgd
end Champernowne
