-- Prove2me | solution 1 for DeletionCode.ConcreteTransitions.ready_base_fill
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:23.169222+00:00
-- url     : https://prove2.me/submissions/2eeaa4cb-dcdf-4a0a-824b-30ba1a39de22

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteTransitions
import Theorems.Thm_DeletionCode_ConcreteTransitions_bankSound_update
import Theorems.Thm_DeletionCode_ConcreteFill_fillFromBase_correct
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_fill_update
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_ready_seedKnown
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
    (x : Letters) (n k : ℕ) (b : B) (w : Slot)
    (hreal : Realizes s mem D k)
    (hs : BankSound mem p (fun a => 3 * (k + 1) + D a))
    (hx : KUnique x n k) (hD : D b < 3 * (k + 1)) (hready : s.Ready b w)
    (hocc : ∃ a, a + 3 * (k + 1) ≤ n ∧
      Agree x a (p b) (windowStart (D b) w) (3 * (k + 1))) :
    ∃ r t, fillFromBase x n k (3 * (k + 1)) (mem b)
        (3 * (k + 1) + D b) (windowStart (D b) w) r = some t ∧
      Realizes (s.fill b w) (Function.update mem b t) D k ∧
      BankSound (Function.update mem b t) p (fun a => 3 * (k + 1) + D a) := by
  obtain ⟨r, seed, hr, hread⟩ :=
    hreal.ready_seedKnown s mem D k b w hD hready
  have hstart := windowStart_le (D b) w
  obtain ⟨t, ht, hsound, hext, hknown⟩ := fillFromBase_correct x (p b)
    n k (3 * (k + 1)) (mem b) (3 * (k + 1) + D b)
    (windowStart (D b) w) r seed hx (hs b) (by omega) hr hread hocc
  exact ⟨r, t, ht,
    Realizes.fill_update s mem D k hreal b w t hext ⟨_, hknown⟩,
    bankSound_update mem p _ hs b t hsound⟩
end DeletionCode.ConcreteTransitions
