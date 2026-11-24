-- Prove2me | solution 1 for FockRL.fi_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:06.173323+00:00
-- url     : https://prove2.me/submissions/9054da72-0e70-4ba7-8d57-a309d60e75c1

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
theorem _root_.solution (hL : FockLinL) (P₁ P₂ Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P₁ + P₂) Q = FockH1Action.fockInner P₁ Q + FockH1Action.fockInner P₂ Q := by
  have h := hL σ 1 P₁ P₂ Q
  simp only [one_smul, map_one, one_mul] at h
  exact h
end FockRL
