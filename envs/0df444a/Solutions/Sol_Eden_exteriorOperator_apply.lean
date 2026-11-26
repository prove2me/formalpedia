-- Prove2me | solution 1 for Eden.exteriorOperator_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:44:52.190697+00:00
-- url     : https://prove2.me/submissions/312963dc-c3b4-4554-9817-f7a1a97b350f

import Definitions.Def_Eden_ExteriorMaximalGrowth
import Definitions.Def_Eden_SelectedProducts
import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_ExteriorOperatorNorm

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (v : ExteriorSpace k) : exteriorOperator k A v = exteriorPower.map k A v := rfl
end Eden
