-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.rebuildPositiveFinite_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:54:19.74462+00:00
-- url     : https://prove2.me/submissions/14ec8b3a-a298-43ed-b524-5fbb2e015e93

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_HeaderRecovery_rebuild_positive_from_known_negative

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (negative : Bits (negativeLength k h))
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hknown : ∀ i : Fin (negativeLength k h), negative i = negativePath k h long i.val) :
    ∀ i : Fin (positiveLength k h),
      rebuildPositiveFinite k h negative i = positivePath k h long i.val := by
  have hknown' : Agree (padBits negative) 0 (negativePath k h long) 0
      (negativeLength k h) := by
    intro i hi
    simpa only [Nat.zero_add, padBits, dif_pos hi] using hknown ⟨i, hi⟩
  have hcorrect := rebuild_positive_from_known_negative k h long (padBits negative)
    hrho0 hrho1 hbit hknown'
  intro i
  simpa only [rebuildPositiveFinite, Nat.zero_add] using hcorrect i.val i.isLt
end DeletionCode.HeaderRecovery
