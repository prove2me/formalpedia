-- Prove2me | solution 1 for DeletionCode.ConcreteModel.Model.sound_update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:14:03.763502+00:00
-- url     : https://prove2.me/submissions/160de3a5-10b8-4339-9a4b-475430b144a2

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_RootSelection
import Definitions.Def_DeletionCode_ConcreteModel

set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteModel
open Windows HeaderRecovery SelectedWindows PartialWords PathMemory ConcreteDecoder
variable {B : Type*} {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteModel
namespace Model
theorem _root_.solution [DecidableEq B] (M : Model B x n k)
    (mem : Bank B) (hs : M.Sound mem) (b : B) (t : Memory)
    (ht : PartialWords.Sound t (negativePath k (M.header b) (M.long b))
      (negativeLength k (M.header b))) : M.Sound (Function.update mem b t) := by
  intro a
  by_cases hab : a = b
  · subst a
    simpa using ht
  · have hba : b ≠ a := Ne.symm hab
    simpa [hab, hba] using hs a
end Model
end DeletionCode.ConcreteModel
