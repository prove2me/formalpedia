-- Prove2me | solution 1 for FockRL.blockDiagonalPreservesDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:24.293506+00:00
-- url     : https://prove2.me/submissions/f5e1aae7-3feb-4e52-8d96-5c5cff80898e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_omAct_eq_sum
import Theorems.Thm_FockRL_omE_apply
import Theorems.Thm_FockRL_X_mul_pderiv_homog
import Theorems.Thm_FockRL_pderiv_X_mul_homog
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
private theorem raiB_apply_of_linePos_eq_false {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = false) (P : FockH1Action.Pol p q r s) :
    FockH1Action.raiB l P = -(pderiv l P) := by
  have h' : ¬ (FockH1Action.linePos l = true) := by simp [h]
  first
  | (rw [FockH1Action.raiB, if_neg h']; done)
  | (rw [FockH1Action.raiB, if_neg h']; rfl)
private theorem lowB_apply_of_linePos_eq_true {l : FockH1Action.Ln p q r s}
    (h : FockH1Action.linePos l = true) (P : FockH1Action.Pol p q r s) :
    FockH1Action.lowB l P = pderiv l P := by
  first
  | (rw [FockH1Action.lowB, if_pos h]; done)
  | (rw [FockH1Action.lowB, if_pos h]; rfl)
private theorem mem_homog_iff_isHomogeneous' {σ : Type} {d : ℕ} {P : MvPolynomial σ ℂ} :
    P ∈ FockH1Action.homog σ d ↔ P.IsHomogeneous d := by
  exact mem_homogeneousSubmodule d P
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
theorem _root_.solution : KCStep := by
  intro p q r s M hM d P hP
  have hP' : P.IsHomogeneous d := mem_homog_iff_isHomogeneous'.mp hP
  rw [omAct_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => ?_
  by_cases h0 : M l l' = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  refine Submodule.smul_mem _ _ ?_
  have hll := hM l l' h0
  rw [omE_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases h1 : FockH1Action.linePos l
    · have h2 : FockH1Action.linePos l' = false := by
        exact hll.symm.trans h1
      rw [raiB_apply_of_linePos_eq_false h1, lowB_apply_of_linePos_eq_false h2]
      exact neg_mem (mem_homog_iff_isHomogeneous'.mpr (pderiv_X_mul_homog l l' hP'))
    · have h2 : FockH1Action.linePos l' = true := by
        exact hll.symm.trans h1
      rw [raiB_apply_of_linePos_eq_true h1, lowB_apply_of_linePos_eq_true h2]
      exact mem_homog_iff_isHomogeneous'.mpr (X_mul_pderiv_homog l l' hP')
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _
end FockRL
