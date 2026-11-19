-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.rebuild_positive_preserves_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:29.94052+00:00
-- url     : https://prove2.me/submissions/614ed3cb-a90d-40a6-b09e-32fd220ff2c5

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header) (p q : Letters)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hknown : Agree p 0 q 0 (negativeLength k h)) :
    Agree (rebuildPositive k h p) 0 (rebuildPositive k h q) 0 (positiveLength k h) := by
  cases ho : h.orientation with
  | deletion =>
    simp only [negativeLength, ho, longLength, windowLength] at hknown
    simp only [rebuildPositive, positiveLength, ho, shortLength, longLength, windowLength]
    intro i hi
    simp only [Nat.zero_add, deleteAt]
    by_cases hleft : i < editOffset k
    · simp only [if_pos hleft]
      simpa only [Nat.zero_add] using hknown i (by omega)
    · simp only [if_neg hleft]
      simpa only [Nat.zero_add] using hknown (i + 1) (by omega)
  | insertion =>
    simp only [negativeLength, ho, shortLength, longLength, windowLength] at hknown
    simp only [rebuildPositive, positiveLength, ho, longLength, windowLength]
    intro i hi
    simp only [Nat.zero_add, insertAt]
    by_cases hleft : i < editOffset k
    · simp only [if_pos hleft]
      have hlt : i < 2 * (3 * (k + 1)) - h.rho - 1 := by
        dsimp [editOffset, windowLength] at hleft
        omega
      simpa only [Nat.zero_add] using hknown i hlt
    · simp only [if_neg hleft]
      by_cases heq : i = editOffset k
      · simp only [if_pos heq]
      · simp only [if_neg heq]
        have hlt : i - 1 < 2 * (3 * (k + 1)) - h.rho - 1 := by
          dsimp [editOffset, windowLength] at hleft heq
          omega
        simpa only [Nat.zero_add] using hknown (i - 1) hlt
end DeletionCode.HeaderRecovery
