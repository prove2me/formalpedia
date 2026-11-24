-- Prove2me | solution 1 for FockRL.omAct_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:21.317852+00:00
-- url     : https://prove2.me/submissions/c83cebf1-11b4-43bc-b454-c9458acd34aa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree

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
theorem _root_.solution (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) :
    FockH1Action.omAct p q r s M = ∑ l, ∑ l', M l l' • FockH1Action.omE l l' := by
  first
  | (simp only [FockH1Action.omAct, LinearMap.coeFn_sum, Finset.sum_apply,
      LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]; done)
  | (simp only [FockH1Action.omAct, LinearMap.sum_apply,
      LinearMap.smulRight_apply, Matrix.entryLinearMap_apply]; done)
end FockRL
