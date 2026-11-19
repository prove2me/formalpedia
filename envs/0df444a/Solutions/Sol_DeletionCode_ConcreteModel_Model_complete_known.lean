-- Prove2me | solution 1 for DeletionCode.ConcreteModel.Model.complete_known
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:56:26.568369+00:00
-- url     : https://prove2.me/submissions/3165e200-df38-486d-b874-06c12ac0e78b

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_RootSelection
import Definitions.Def_DeletionCode_ConcreteModel
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeExtra_lt
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeLength_eq
import Theorems.Thm_DeletionCode_SelectedWindows_Realizes_complete_wordKnown


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteModel
open Windows HeaderRecovery SelectedWindows PartialWords PathMemory ConcreteDecoder
variable {B : Type*} {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteModel
namespace Model
theorem _root_.solution (M : Model B x n k) (s : Recovery.State B)
    (mem : Bank B) (hreal : M.Realizes s mem) (b : B) (hc : s.Complete b) :
    WindowKnown (mem b) 0 (negativeLength k (M.header b)) := by
  rw [negativeLength_eq k (M.header b) (M.rho_lower b) (M.rho_upper b)]
  exact hreal.complete_wordKnown s mem (fun b => negativeExtra k (M.header b)) k
    b (Nat.le_of_lt (negativeExtra_lt k (M.header b) (M.rho_lower b) (M.rho_upper b))) hc
end Model
end DeletionCode.ConcreteModel
