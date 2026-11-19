-- Prove2me | solution 1 for DeletionCode.Windows.deletion_crossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:19.576167+00:00
-- url     : https://prove2.me/submissions/97451186-4d04-4551-8c00-86c6074dbf1e

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell s k : ℕ)
    (hs : s ≤ ell) (he : ell < s + k) :
    ∀ i, i < k → deleteAt p ell (s + i) =
      deletionSeed k (ell - s) (deleteAt p ell (s + k - 1))
        (fun j => p (s + j)) i := by
  intro i hi
  unfold deletionSeed
  by_cases hcut : i < ell - s
  · have hidx : s + i < ell := by omega
    simp [hcut, deleteAt, hidx]
  · by_cases hlast : i + 1 < k
    · have hidx : ¬ s + i < ell := by omega
      simp [hcut, hlast, deleteAt, hidx, Nat.add_assoc]
    · have hidx : s + i = s + k - 1 := by omega
      simp only [if_neg hcut, if_neg hlast]
      exact congrArg (deleteAt p ell) hidx
end DeletionCode.Windows
