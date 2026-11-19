-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.negativeExtra_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:08:17.537202+00:00
-- url     : https://prove2.me/submissions/f029248f-b85f-49ae-9fa5-e2e4db97420d

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1) :
    negativeExtra k h < windowLength k := by
  unfold negativeExtra
  cases ho : h.orientation <;>
    simp only [negativeLength, ho, shortLength, longLength, windowLength] <;> omega
end DeletionCode.HeaderRecovery
