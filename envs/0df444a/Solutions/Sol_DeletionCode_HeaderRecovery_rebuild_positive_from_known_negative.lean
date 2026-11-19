-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.rebuild_positive_from_known_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:53:55.275009+00:00
-- url     : https://prove2.me/submissions/663f1183-c628-4d12-a7c0-7b3d1df1c7e6

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_HeaderRecovery_rebuild_positive_correct
import Theorems.Thm_DeletionCode_HeaderRecovery_rebuild_positive_preserves_agreement

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header)
    (long known : Letters)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hknown : Agree known 0 (negativePath k h long) 0 (negativeLength k h)) :
    Agree (rebuildPositive k h known) 0 (positivePath k h long) 0 (positiveLength k h) := by
  rw [← rebuild_positive_correct k h long hbit]
  exact rebuild_positive_preserves_agreement k h known (negativePath k h long)
    hrho0 hrho1 hknown
end DeletionCode.HeaderRecovery
