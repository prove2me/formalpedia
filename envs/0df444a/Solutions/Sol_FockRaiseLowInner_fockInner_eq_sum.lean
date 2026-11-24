-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:51.450004+00:00
-- url     : https://prove2.me/submissions/5af625c2-331f-4bc5-a925-7fb3767911f8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}
namespace FockRaiseLowInner
theorem _root_.solution (P Q : MvPolynomial σ ℂ) (S : Finset (σ →₀ ℕ))
    (hS : ∀ α, α ∉ S → (starRingEnd ℂ) (coeff α P) * coeff α Q = 0) :
    fockInner P Q = ∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
  classical
  rw [fockInner_eq_support]
  have h1 : (∑ α ∈ P.support, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α) =
      ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    refine Finset.sum_subset (fun x hx => Finset.mem_union_left _ hx) (fun α _ hα => ?_)
    have h : coeff α P = 0 := by simpa [MvPolynomial.mem_support_iff] using hα
    rw [h]
    simp
  have h2 : (∑ α ∈ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α) =
      ∑ α ∈ P.support ∪ S, (starRingEnd ℂ) (coeff α P) * coeff α Q * wt α := by
    refine Finset.sum_subset (fun x hx => Finset.mem_union_right _ hx) (fun α _ hα => ?_)
    rw [hS α hα, zero_mul]
  rw [h1, h2]
end FockRaiseLowInner
