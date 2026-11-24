-- Prove2me | solution 1 for FockRL.fi_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:44.326854+00:00
-- url     : https://prove2.me/submissions/1efae00a-412b-4252-8f69-eec4ac31ed16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_fi_zero_left

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
theorem _root_.solution (hL : FockLinL) (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q := by
  have h := hL σ c P 0 Q
  simp only [add_zero, fi_zero_left] at h
  exact h
end FockRL
