-- Prove2me | solution 1 for FockRL.fi_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:06.534493+00:00
-- url     : https://prove2.me/submissions/f087f3a1-02e4-4ee5-ab73-eae3af402cd0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_fi_zero_right

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
variable {σ : Type}
namespace FockRL
theorem _root_.solution (hR : FockLinR) (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (c • Q) = c * FockH1Action.fockInner P Q := by
  have h := hR σ c P Q 0
  simp only [add_zero, fi_zero_right] at h
  exact h
end FockRL
