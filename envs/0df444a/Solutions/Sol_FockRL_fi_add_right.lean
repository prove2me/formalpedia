-- Prove2me | solution 1 for FockRL.fi_add_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:44.096866+00:00
-- url     : https://prove2.me/submissions/60aa7f32-66d4-4c72-ab61-6b405cead663

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
variable {σ : Type}
namespace FockRL
theorem _root_.solution (hR : FockLinR) (P Q₁ Q₂ : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (Q₁ + Q₂) = FockH1Action.fockInner P Q₁ + FockH1Action.fockInner P Q₂ := by
  have h := hR σ 1 P Q₁ Q₂
  simp only [one_smul, one_mul] at h
  exact h
end FockRL
