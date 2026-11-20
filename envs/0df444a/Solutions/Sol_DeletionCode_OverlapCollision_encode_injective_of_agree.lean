-- Prove2me | solution 1 for DeletionCode.OverlapCollision.encode_injective_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:46.77542+00:00
-- url     : https://prove2.me/submissions/eae956e9-130a-4715-adf1-35d1a9dc3a27

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision
import Theorems.Thm_DeletionCode_OverlapCollision_encode_eq_at

set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery
namespace DeletionCode.OverlapCollision
theorem _root_.solution (n k a b : ℕ) (hab : a < b)
    (hb : b + k ≤ n) (x y : Bits n)
    (hx : Agree (padBits x) a (padBits x) b k)
    (hy : Agree (padBits y) a (padBits y) b k)
    (heq : encode n k b hb x = encode n k b hb y) : x = y := by
  have hall : ∀ j, j < n → padBits x j = padBits y j := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      by_cases hbefore : j < b
      · exact encode_eq_at n k b hb x y heq j hj (Or.inl hbefore)
      by_cases hafter : b + k ≤ j
      · exact encode_eq_at n k b hb x y heq j hj (Or.inr hafter)
      have hoffset : j - b < k := by omega
      have hearlier : a + (j - b) < j := by omega
      have hearlier_bound : a + (j - b) < n := by omega
      have hrestore : b + (j - b) = j := by omega
      have hxcopy := hx (j - b) hoffset
      have hycopy := hy (j - b) hoffset
      rw [hrestore] at hxcopy hycopy
      exact hxcopy.symm.trans ((ih (a + (j - b)) hearlier hearlier_bound).trans hycopy)
  funext j
  simpa only [padBits, dif_pos j.isLt] using hall j.val j.isLt
end DeletionCode.OverlapCollision
