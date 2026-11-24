-- Prove2me | solution 1 for FockRL.omE_pos_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:06.906327+00:00
-- url     : https://prove2.me/submissions/349a853e-55c3-420b-bd72-7204be48eb9b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_omE_apply
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
private theorem raiB_apply_of_linePos_eq_true {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) (P : FockH1Action.Pol p q r s) :
    FockH1Action.raiB l P = X l * P := by
  first
  | (rw [FockH1Action.raiB, if_pos h]; done)
  | (rw [FockH1Action.raiB, if_pos h]; rfl)
private theorem lowB_apply_of_linePos_eq_false {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) (P : FockH1Action.Pol p q r s) :
    FockH1Action.lowB l P = X l * P := by
  have h' : ¬ (FockH1Action.linePos l = true) := by simp [h]
  first
  | (rw [FockH1Action.lowB, if_neg h']; done)
  | (rw [FockH1Action.lowB, if_neg h']; rfl)
section Inner
variable {σ : Type}
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
theorem _root_.solution {l l' : FockH1Action.Ln p q r s} (h1 : FockH1Action.linePos l = true)
    (h2 : FockH1Action.linePos l' = false) (P : FockH1Action.Pol p q r s) :
    FockH1Action.omE l l' P = X l * (X l' * P) := by
  have hne : l ≠ l' := by
    rintro rfl
    simp_all
  rw [omE_apply, if_neg hne, add_zero, lowB_apply_of_linePos_eq_false h2, raiB_apply_of_linePos_eq_true h1]
end FockRL
