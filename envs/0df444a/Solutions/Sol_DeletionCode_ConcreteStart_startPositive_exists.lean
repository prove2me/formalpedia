-- Prove2me | solution 1 for DeletionCode.ConcreteStart.startPositive_exists
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:56.039047+00:00
-- url     : https://prove2.me/submissions/3937d361-e333-416e-a06e-0dbba68e07ef

import Definitions.Def_DeletionCode_HeaderRecovery
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteStart
import Theorems.Thm_DeletionCode_ConcreteStart_startPositive_correct

set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteStart
open Windows PartialWords SelectedWindows
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  transferFinite windowLength editOffset negativeExtra)
namespace DeletionCode.ConcreteStart
theorem _root_.solution (k : ℕ) (h : Header) (long : Letters)
    (offset : ℕ) (bits : PartialWords.Bits k) (s : Memory)
    (hrho0 : 1 ≤ h.rho) (hrho1 : h.rho ≤ k + 1)
    (hbit : long (editOffset k) = h.bit)
    (hs : Sound s (negativePath k h long) (negativeLength k h))
    (hbound : offset + k ≤ positiveLength k h)
    (hseed : ∀ i : Fin k, positivePath k h long (offset + i.val) = bits i) :
    ∃ extra t, startPositive k h offset bits extra s = some t ∧
      StartedCorrectly k h long s t := by
  let extra := negativePath k h long (offset + k - 1)
  obtain ⟨t, ht, hcorrect⟩ := startPositive_correct k h long offset bits extra s
    hrho0 hrho1 hbit hs hbound hseed (fun _ _ _ => rfl)
  exact ⟨extra, t, ht, hcorrect⟩
end DeletionCode.ConcreteStart
