-- Prove2me | solution 1 for Champernowne.card_mDigit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:33.496255+00:00
-- url     : https://prove2.me/submissions/dc407f92-0c7b-4d3b-8305-aae14363c1b8

module
public import Definitions.Def_LeanPool_Champernowne_Count
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_Champernowne_DigitCount

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b : ℕ} (hb : 1 < b) (m : ℕ) (hm : 0 < m) :
    (Finset.Ico (b ^ (m - 1)) (b ^ m)).card = (b - 1) * b ^ (m - 1) := by
  rw [Nat.card_Ico]
  have h : b ^ m = b * b ^ (m - 1) := by
    conv_lhs => rw [show m = (m - 1) + 1 by omega]
    rw [pow_succ']
  have hd : (b - 1) * b ^ (m - 1) + b ^ (m - 1) = b * b ^ (m - 1) := by
    have hb1 : b - 1 + 1 = b := by omega
    calc (b - 1) * b ^ (m - 1) + b ^ (m - 1)
        = (b - 1 + 1) * b ^ (m - 1) := by ring
    _ = b * b ^ (m - 1) := by rw [hb1]
  omega
end Champernowne
