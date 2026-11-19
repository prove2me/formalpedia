-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.transfer_positive_seed_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:03.105454+00:00
-- url     : https://prove2.me/submissions/8755873a-feac-4188-b466-4380737b59e2

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_HeaderRecovery_transfer_positive_seed_correct
import Theorems.Thm_DeletionCode_HeaderRecovery_transfer_positive_seed_in_bounds

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (seed : Seed) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hbound : seed.offset + k ≤ positiveLength k h)
    (hseed : Agree (positivePath k h long) seed.offset seed.bits 0 k)
    (hextra : ExtensionMatches k h long seed extra) :
    (transferPositiveSeed k h seed extra).offset + k ≤ negativeLength k h ∧
      Agree (negativePath k h long) (transferPositiveSeed k h seed extra).offset
        (transferPositiveSeed k h seed extra).bits 0 k := by
  exact ⟨transfer_positive_seed_in_bounds k h seed extra hrho0 hrho1 hbound,
    transfer_positive_seed_correct k h long seed extra hbit hseed hextra⟩
end DeletionCode.HeaderRecovery
