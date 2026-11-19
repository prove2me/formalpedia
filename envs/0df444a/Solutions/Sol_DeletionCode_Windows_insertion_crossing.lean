-- Prove2me | solution 1 for DeletionCode.Windows.insertion_crossing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:50:40.523324+00:00
-- url     : https://prove2.me/submissions/ca41a2c6-bcc2-4181-9904-04ccba246595

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_Windows

set_option autoImplicit true
open DeletionCode DeletionCode.Windows
namespace DeletionCode.Windows
theorem _root_.solution (p : Letters) (ell s k : ℕ) (d : Bool)
    (hs : s ≤ ell) :
    ∀ i, i < k → insertAt p ell d (s + i) =
      insertionSeed (ell - s) d (fun j => p (s + j)) i := by
  intro i hi
  unfold insertionSeed
  by_cases hcut : i < ell - s
  · have hidx : s + i < ell := by omega
    simp [hcut, insertAt, hidx]
  · by_cases heq : i = ell - s
    · have hidx : s + i = ell := by omega
      simp only [if_neg hcut, if_pos heq]
      simp [insertAt, hidx]
    · have hlt : ¬ s + i < ell := by omega
      have hne : s + i ≠ ell := by omega
      have hidx : s + i - 1 = s + (i - 1) := by omega
      simp [hcut, heq, insertAt, hlt, hne, hidx]
end DeletionCode.Windows
