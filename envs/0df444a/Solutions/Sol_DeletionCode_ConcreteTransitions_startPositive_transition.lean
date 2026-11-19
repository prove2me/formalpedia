-- Prove2me | solution 1 for DeletionCode.ConcreteTransitions.startPositive_transition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:57:42.495337+00:00
-- url     : https://prove2.me/submissions/d6772523-2952-41b6-b665-4df2b36c85d8

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteTransitions
import Theorems.Thm_DeletionCode_ConcreteTransitions_bankSound_update
import Theorems.Thm_DeletionCode_ConcreteStart_startPositive_exists
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_start_update


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteTransitions
open Windows PartialWords Recovery SelectedWindows ConcreteFill ConcreteStart
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  negativeExtra editOffset)
variable {B : Type*}
namespace DeletionCode.ConcreteTransitions
theorem _root_.solution [DecidableEq B]
    (s : State B) (mem : B → Memory) (headers : B → Header) (long : B → Letters)
    (k : ℕ) (b : B) (offset : ℕ) (bits : Bits k)
    (hreal : Realizes s mem (fun a => negativeExtra k (headers a)) k)
    (hs : BankSound mem (fun a => negativePath k (headers a) (long a))
      (fun a => negativeLength k (headers a)))
    (hrho0 : 1 ≤ (headers b).rho) (hrho1 : (headers b).rho ≤ k + 1)
    (hbit : long b (editOffset k) = (headers b).bit)
    (hbound : offset + k ≤ positiveLength k (headers b))
    (hseed : ∀ i : Fin k, positivePath k (headers b) (long b) (offset + i.val) = bits i) :
    ∃ extra w t, startPositive k (headers b) offset bits extra (mem b) = some t ∧
      Realizes (s.start b w) (Function.update mem b t)
        (fun a => negativeExtra k (headers a)) k ∧
      BankSound (Function.update mem b t)
        (fun a => negativePath k (headers a) (long a)) (fun a => negativeLength k (headers a)) := by
  obtain ⟨extra, t, ht, hsound, hext, w, hknown⟩ := startPositive_exists
    k (headers b) (long b) offset bits (mem b) hrho0 hrho1 hbit (hs b) hbound hseed
  exact ⟨extra, w, t, ht,
    Realizes.start_update s mem _ k hreal b w t hext hknown,
    bankSound_update mem _ _ hs b t hsound⟩
end DeletionCode.ConcreteTransitions
