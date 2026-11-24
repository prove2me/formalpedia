-- Prove2me | solution 1 for FockRL.Rop_raise
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:41:55.355241+00:00
-- url     : https://prove2.me/submissions/6241a1a6-a2a3-4763-a092-0d18c9a067ec

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_BlockDiagonalPreservesDegree
import Theorems.Thm_FockRL_Rop_apply
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
private theorem mem_homog_iff_isHomogeneous' {σ : Type} {d : ℕ} {P : MvPolynomial σ ℂ} :
    P ∈ FockH1Action.homog σ d ↔ P.IsHomogeneous d := by
  exact mem_homogeneousSubmodule d P
private theorem isHomogeneous_X_complex {σ : Type} (l : σ) : (X l : MvPolynomial σ ℂ).IsHomogeneous 1 := by
  exact isHomogeneous_X ℂ l
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
theorem _root_.solution (M : Matrix (FockH1Action.Ln p q r s) (FockH1Action.Ln p q r s) ℂ) (d : ℕ)
    (P : FockH1Action.Pol p q r s) (hP : P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) d) :
    Rop M P ∈ FockH1Action.homog (FockH1Action.Ln p q r s) (d + 2) := by
  rw [Rop_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => ?_
  split_ifs
  · refine Submodule.smul_mem _ _ (mem_homog_iff_isHomogeneous'.mpr ?_)
    have h := (isHomogeneous_X_complex l).mul ((isHomogeneous_X_complex l').mul (mem_homog_iff_isHomogeneous'.mp hP))
    rwa [show 1 + (1 + d) = d + 2 by omega] at h
  · exact Submodule.zero_mem _
end FockRL
