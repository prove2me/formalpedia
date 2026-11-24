-- Prove2me | solution 1 for FockRL.fi_Rop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:13.499823+00:00
-- url     : https://prove2.me/submissions/be7fc15c-1cdc-4568-8f10-8083801aa4d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_Rop_apply
import Theorems.Thm_FockRL_fi_zero_left
import Theorems.Thm_FockRL_fi_smul_left
import Theorems.Thm_FockRL_fi_sum_left

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
theorem _root_.solution (hL : FockLinL) (hX : FockXAdj)
    (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (P Q : FockH1Action.Pol p q r s) :
    FockH1Action.fockInner (Rop M P) Q = ∑ l, ∑ l', if FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false
      then (starRingEnd ℂ) (M l l') * FockH1Action.fockInner P (pderiv l' (pderiv l Q)) else 0 := by
  rw [Rop_apply, fi_sum_left hL]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fi_sum_left hL]
  refine Finset.sum_congr rfl fun l' _ => ?_
  split_ifs
  · rw [fi_smul_left hL, hX _ l, hX _ l']
  · exact fi_zero_left Q
end FockRL
