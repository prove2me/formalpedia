-- Prove2me | solution 1 for DeletionCode.GeneratingModel.EditedFamily.negative_extra
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:24.159289+00:00
-- url     : https://prove2.me/submissions/f217149f-f583-400b-88a2-b8486ef1471c

import Definitions.Def_DeletionCode_ConcreteModel
import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Data.Fintype.Quotient
import Definitions.Def_DeletionCode_GeneratingModel

set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingModel
open Windows HeaderRecovery PathMemory SelectedWindows RootSelection ConcreteModel
variable {B : Type*} {k : ℕ}
namespace DeletionCode.GeneratingModel
namespace EditedFamily
theorem _root_.solution (E : EditedFamily B k) (b : B) :
    E.family.extra b false = negativeExtra k (E.header b) := rfl
end EditedFamily
end DeletionCode.GeneratingModel
