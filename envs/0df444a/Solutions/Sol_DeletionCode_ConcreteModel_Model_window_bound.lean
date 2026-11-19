-- Prove2me | solution 1 for DeletionCode.ConcreteModel.Model.window_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:13:57.318346+00:00
-- url     : https://prove2.me/submissions/1618b26c-2810-4f39-b257-9e52d34c1249

import Definitions.Def_DeletionCode_ConcreteDecoder
import Definitions.Def_DeletionCode_RootSelection
import Definitions.Def_DeletionCode_ConcreteModel
import Theorems.Thm_DeletionCode_HeaderRecovery_negativeLength_eq
import Theorems.Thm_DeletionCode_SelectedWindows_windowStart_le


set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteModel
open Windows HeaderRecovery SelectedWindows PartialWords PathMemory ConcreteDecoder
variable {B : Type*} {x : Letters} {n k : ℕ}
namespace DeletionCode.ConcreteModel
namespace Model
theorem _root_.solution (M : Model B x n k) (b : B) (w : Recovery.Slot) :
    windowStart (negativeExtra k (M.header b)) w + windowLength k ≤
      negativeLength k (M.header b) := by
  rw [negativeLength_eq k (M.header b) (M.rho_lower b) (M.rho_upper b)]
  have := windowStart_le (negativeExtra k (M.header b)) w
  omega
end Model
end DeletionCode.ConcreteModel
