-- Prove2me | solution 1 for FockRL.Rop_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:45.301527+00:00
-- url     : https://prove2.me/submissions/7fbf0c2f-008e-4f63-8771-72a513239eb4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_omE_pos_neg

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
theorem _root_.solution (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P : FockH1Action.Pol p q r s) :
    Rop M P = ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false then
      M l l' • (X l * (X l' * P)) else 0 := by
  unfold Rop
  simp only [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  split_ifs with h
  · rw [LinearMap.smul_apply, omE_pos_neg h.1 h.2]
  · rfl
end FockRL
