-- Prove2me | solution 1 for DeletionCode.HeaderRecovery.transferFinite_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:55:40.109337+00:00
-- url     : https://prove2.me/submissions/d5f749f7-763f-4929-9af2-716a1a6b7966

import Definitions.Def_DeletionCode_Windows
import Definitions.Def_DeletionCode_HeaderRecovery
import Theorems.Thm_DeletionCode_HeaderRecovery_transfer_positive_seed_valid

set_option autoImplicit true
open DeletionCode DeletionCode.HeaderRecovery
open Windows
namespace DeletionCode.HeaderRecovery
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : Bits k) (extra : Bool)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i)
    (hextra : h.orientation = .insertion → offset ≤ editOffset k →
      editOffset k < offset + k →
        extra = negativePath k h long (offset + k - 1)) :
    (transferFinite k h offset bits extra).1 + k ≤ negativeLength k h ∧
      ∀ i : Fin k,
        negativePath k h long ((transferFinite k h offset bits extra).1 + i.val) =
          (transferFinite k h offset bits extra).2 i := by
  have hseed' : Agree (positivePath k h long) offset (padBits bits) 0 k := by
    intro i hi
    simpa only [Nat.zero_add, padBits, dif_pos hi] using hseed ⟨i, hi⟩
  have hextra' : ExtensionMatches k h long ⟨offset, padBits bits⟩ extra := by
    exact hextra
  have hvalid := transfer_positive_seed_valid k h long ⟨offset, padBits bits⟩ extra
    hrho0 hrho1 hbit hbound hseed' hextra'
  refine ⟨hvalid.1, ?_⟩
  intro i
  simpa only [transferFinite, Nat.zero_add] using hvalid.2 i.val i.isLt
end DeletionCode.HeaderRecovery
