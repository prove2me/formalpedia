-- Prove2me | solution 1 for FockRL.fi_Lop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:08.608989+00:00
-- url     : https://prove2.me/submissions/6dddbc65-2c80-401f-a2de-2d408e64475f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_Lop_apply
import Theorems.Thm_FockRL_fi_zero_right
import Theorems.Thm_FockRL_fi_smul_right
import Theorems.Thm_FockRL_fi_sum_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial
namespace FockRL
variable {p q r s : ℕ}
section Inner
variable {σ : Type}
private theorem fockInner_neg_right' (hR : FockLinR) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner P (-Q) = -FockH1Action.fockInner P Q := by
  have h := fi_smul_right hR (-1 : ℂ) P Q
  rw [neg_one_smul, neg_one_mul] at h
  exact h
end Inner
end FockRL
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial
open FockRL
variable {p q r s : ℕ}
namespace FockRL
theorem _root_.solution (hR : FockLinR)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P Q : FockH1Action.Pol p q r s) :
    FockH1Action.fockInner P (Lop M Q) = ∑ l, ∑ l', if FockH1Action.linePos l = false ∧ FockH1Action.linePos l' = true
      then -(M l l' * FockH1Action.fockInner P (pderiv l (pderiv l' Q))) else 0 := by
  rw [Lop_apply, fi_sum_right hR]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fi_sum_right hR]
  refine Finset.sum_congr rfl fun l' _ => ?_
  split_ifs
  · rw [fi_smul_right hR, fockInner_neg_right' hR, mul_neg]
  · exact fi_zero_right P
end FockRL
