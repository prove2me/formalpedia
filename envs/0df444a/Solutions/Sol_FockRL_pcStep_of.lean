-- Prove2me | solution 1 for FockRL.pcStep_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:07.432803+00:00
-- url     : https://prove2.me/submissions/0c067dc2-59c7-44b0-b35a-2cff49d1a88b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_omAct_eq_Rop_add_Lop
import Theorems.Thm_FockRL_Rop_raise
import Theorems.Thm_FockRL_Lop_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open FockRL
variable {p q r s : ℕ}
namespace FockRL
theorem _root_.solution (hS : PMSplit) : PCStep := by
  intro p q r s M hM P
  have h := hS _ (Rop M) (Lop M) (Rop_raise M)
    (Lop_shift M) P
  rw [omAct_eq_Rop_add_Lop M hM, h.1, h.2, LinearMap.add_apply]
end FockRL
