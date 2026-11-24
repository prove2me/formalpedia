-- Prove2me | solution 1 for FockRL.adjStep_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:05:16.836303+00:00
-- url     : https://prove2.me/submissions/23eec2c3-45d7-40a8-b3c6-53247b290fd4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_omAct_eq_Rop_add_Lop
import Theorems.Thm_FockRL_Rop_raise
import Theorems.Thm_FockRL_Lop_shift
import Theorems.Thm_FockRL_fi_Rop
import Theorems.Thm_FockRL_fi_Lop

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
theorem _root_.solution (hS : PMSplit) (hL : FockLinL) (hR : FockLinR) (hX : FockXAdj) : AdjStep := by
  intro p q r s M M' hM hM' hA P Q
  have e1 := (hS _ (Rop M) (Lop M) (Rop_raise M)
    (Lop_shift M) P).1
  have e2 := (hS _ (Rop M') (Lop M') (Rop_raise M')
    (Lop_shift M') Q).2
  rw [omAct_eq_Rop_add_Lop M hM,
    omAct_eq_Rop_add_Lop M' hM', e1, e2,
    fi_Rop hL hX, fi_Lop hR]
  simp only [← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  by_cases h : FockH1Action.linePos l = true ∧ FockH1Action.linePos l' = false
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, hA l l' h.1 h.2, neg_neg]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), neg_zero]
end FockRL
