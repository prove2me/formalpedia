-- Prove2me | solution 1 for DeletionCode.ConcreteTransitions.bankSound_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:08:53.057066+00:00
-- url     : https://prove2.me/submissions/cf3f6707-9e75-484b-853f-a466d91b6799

import Definitions.Def_DeletionCode_ConcreteFill
import Definitions.Def_DeletionCode_ConcreteStart
import Definitions.Def_DeletionCode_SelectedWindows
import Definitions.Def_DeletionCode_ConcreteTransitions

set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteTransitions
open Windows PartialWords Recovery SelectedWindows ConcreteFill ConcreteStart
open HeaderRecovery (Header negativePath positivePath negativeLength positiveLength
  negativeExtra editOffset)
variable {B : Type*}
namespace DeletionCode.ConcreteTransitions
theorem _root_.solution [DecidableEq B] (mem : B → Memory) (p : B → Letters)
    (len : B → ℕ) (hs : BankSound mem p len) (b : B) (t : Memory)
    (ht : Sound t (p b) (len b)) : BankSound (Function.update mem b t) p len := by
  intro a
  by_cases hab : a = b
  · subst a
    simpa using ht
  · have hba : b ≠ a := Ne.symm hab
    simpa [Function.update, hab, hba] using hs a
end DeletionCode.ConcreteTransitions
