-- Prove2me | solution 1 for DeletionCode.ConcreteTransitions.complete_supplier_fill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:23.730701+00:00
-- url     : https://prove2.me/submissions/6cdf6575-20c2-4ccc-8dc1-874d968a6217

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteTransitions
import Theorems.Thm_DeletionCode_ConcreteTransitions_bankSound_update
import Theorems.Thm_DeletionCode_ConcreteFill_copyFromMemory_correct
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_complete_wordKnown
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_fill_update
import Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_subblock
import Theorems.Thm_DeletionCode_SelectedWindows_windowStart_le


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteTransitions
open Windows PartialWords Recovery SelectedWindows ConcreteFill ConcreteStart
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  negativeExtra editOffset)
variable {B : Type*}
namespace DeletionCode.ConcreteTransitions
theorem _root_.solution [DecidableEq B]
    (s : State B) (mem : B → Memory) (D : B → ℕ) (p : B → Letters)
    (k : ℕ) (a b : B) (w : Slot) (sourceStart : ℕ)
    (hreal : Realizes s mem D k)
    (hs : BankSound mem p (fun c => 3 * (k + 1) + D c))
    (hD : D a ≤ 3 * (k + 1)) (hcomplete : s.Complete a)
    (hsource : sourceStart ≤ D a)
    (hagree : Agree (p a) sourceStart (p b) (windowStart (D b) w) (3 * (k + 1))) :
    ∃ t, copyFromMemory (mem a) (3 * (k + 1) + D a) sourceStart (3 * (k + 1))
        (mem b) (3 * (k + 1) + D b) (windowStart (D b) w) = some t ∧
      Realizes (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun c => 3 * (k + 1) + D c) := by
  have hwhole := hreal.complete_wordKnown s mem D k a hD hcomplete
  obtain ⟨bits, hread⟩ := windowKnown_subblock (mem a) 0
    (3 * (k + 1) + D a) sourceStart (3 * (k + 1)) hwhole (by omega) (by omega)
  have hstart := windowStart_le (D b) w
  obtain ⟨t, ht, hsound, hext, hknown⟩ := copyFromMemory_correct
    (mem a) (mem b) (p a) (p b) (3 * (k + 1) + D a) sourceStart
    (3 * (k + 1)) (3 * (k + 1) + D b) (windowStart (D b) w) bits
    (hs a) (hs b) (by omega) (by omega) hread hagree
  exact ⟨t, ht,
    Realizes.fill_update s mem D k hreal b w t hext ⟨_, hknown⟩,
    bankSound_update mem p _ hs b t hsound⟩
end DeletionCode.ConcreteTransitions
