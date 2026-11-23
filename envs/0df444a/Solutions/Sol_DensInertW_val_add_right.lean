-- Prove2me | solution 1 for DensInertW.val_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:33.330501+00:00
-- url     : https://prove2.me/submissions/1939833f-b16b-4fc8-a438-d0b8dcaaedc6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Theorems.Thm_DensInertW_frob_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}
namespace DensInertW
theorem _root_.solution (x y y' : Fin n → L) :
    hf (Fintype.card K) M x (y + y') =
      hf (Fintype.card K) M x y + hf (Fintype.card K) M x y' := by
  simp only [hf, Pi.add_apply, frob_add, mul_add, Finset.sum_add_distrib]
end DensInertW
