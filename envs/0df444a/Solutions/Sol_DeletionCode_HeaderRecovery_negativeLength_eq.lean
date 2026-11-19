-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.negativeLength_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:08:15.569199+00:00
-- url     : https://prove2.me/submissions/402268d3-fd32-40d3-8be8-82b8d8113684

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1) :
    negativeLength k h = windowLength k + negativeExtra k h := by
  unfold negativeExtra
  cases ho : h.orientation <;>
    simp only [negativeLength, ho, shortLength, longLength, windowLength] <;> omega
end DeletionCode.HeaderRecovery
