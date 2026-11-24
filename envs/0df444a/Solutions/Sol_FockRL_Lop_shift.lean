-- Prove2me | solution 1 for FockRL.Lop_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:49.087739+00:00
-- url     : https://prove2.me/submissions/bcdfc720-2898-4c8d-af9d-cc351bfdda7c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_Lop_apply
import Theorems.Thm_FockRL_hc_pderiv

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
theorem _root_.solution (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (e : ℕ)
    (P : FockH1Action.Pol p q r s) :
    homogeneousComponent e (Lop M P) = Lop M (homogeneousComponent (e + 2) P) := by
  rw [show e + 2 = e + 1 + 1 from rfl, Lop_apply, Lop_apply, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l' _ => ?_
  split_ifs
  · rw [map_smul, map_neg, hc_pderiv, hc_pderiv]
  · exact map_zero _
end FockRL
