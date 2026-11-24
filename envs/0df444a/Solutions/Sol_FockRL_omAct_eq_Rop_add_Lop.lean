-- Prove2me | solution 1 for FockRL.omAct_eq_Rop_add_Lop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:11.239138+00:00
-- url     : https://prove2.me/submissions/55897521-b700-433e-8cf4-2ca68ea5231b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_omAct_eq_sum

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
theorem _root_.solution (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ)
    (hM : OppSign M) : FockH1Action.omAct p q r s M = Rop M + Lop M := by
  rw [omAct_eq_sum]
  unfold Rop Lop
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases h0 : M l l' = 0
  · simp [h0]
  · have hd := hM l l' h0
    cases h1 : FockH1Action.linePos l <;>
      cases h2 : FockH1Action.linePos l' <;> simp_all
end FockRL
