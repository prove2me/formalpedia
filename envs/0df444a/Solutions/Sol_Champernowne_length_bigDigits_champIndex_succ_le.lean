-- Prove2me | solution 1 for Champernowne.length_bigDigits_champIndex_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:36.946586+00:00
-- url     : https://prove2.me/submissions/07d7dab3-3ee4-42c2-823e-ee1e0fac6a42

module
public import Definitions.Def_LeanPool_Champernowne_DigitCount
public import Definitions.Def_LeanPool_Champernowne_Prefix
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Definitions.Def_LeanPool_Champernowne_Positions

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b n M : ℕ} (hb : 1 < b)
    (h2 : champIndex b n + 1 ≤ b ^ M) :
    (bigDigits b (champIndex b n + 1)).length ≤ M + 1 := by
  rw [bigDigits, List.length_reverse]
  refine (Nat.digits_length_le_iff hb _).mpr ?_
  calc champIndex b n + 1 ≤ b ^ M := h2
  _ < b ^ (M + 1) := Nat.pow_lt_pow_right hb (Nat.lt_succ_self M)
end Champernowne
