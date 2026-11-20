-- Prove2me | solution 1 for DeletionCode.OverlapCollision.encode_eq_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:29.555146+00:00
-- url     : https://prove2.me/submissions/e1208e4e-78cd-443d-9b5f-148311b800a7

import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_OverlapCollision

set_option autoImplicit true
open DeletionCode DeletionCode.OverlapCollision
open Windows HeaderRecovery
namespace DeletionCode.OverlapCollision
theorem _root_.solution (n k b : ℕ) (hb : b + k ≤ n)
    (x y : Bits n) (heq : encode n k b hb x = encode n k b hb y)
    (j : ℕ) (hj : j < n) (hout : j < b ∨ b + k ≤ j) :
    padBits x j = padBits y j := by
  rcases hout with hbefore | hafter
  · have hj' : j < n - k := by omega
    have hh := congrFun heq (⟨j, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_pos hbefore, padBits, dif_pos hj] using hh
  · have hj' : j - k < n - k := by omega
    have hbefore : ¬j - k < b := by omega
    have hrestore : j - k + k = j := by omega
    have hh := congrFun heq (⟨j - k, hj'⟩ : Fin (n - k))
    simpa only [encode, keptIndex, dif_neg hbefore, hrestore,
      padBits, dif_pos hj] using hh
end DeletionCode.OverlapCollision
