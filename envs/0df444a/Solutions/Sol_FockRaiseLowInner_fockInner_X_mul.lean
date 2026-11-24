-- Prove2me | solution 1 for FockRaiseLowInner.fockInner_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:42.988077+00:00
-- url     : https://prove2.me/submissions/7558d9f2-ec33-4835-aec0-d187a71134e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_sum_right
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_wt_single_add

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
theorem _root_.solution (l : σ) (P Q : MvPolynomial σ ℂ) :
    fockInner (X l * P) Q = fockInner P (pderiv l Q) := by
  classical
  refine MvPolynomial.induction_on' Q (fun β b => ?_) (fun Q₁ Q₂ h₁ h₂ => ?_)
  · rw [pderiv_monomial,
      fockInner_eq_sum_right (X l * P) (monomial β b) {β} support_monomial_subset,
      fockInner_eq_sum_right P (monomial (β - Finsupp.single l 1) (b * (β l : ℂ)))
        {β - Finsupp.single l 1} support_monomial_subset,
      Finset.sum_singleton, Finset.sum_singleton, coeff_monomial, coeff_monomial, if_pos rfl, if_pos rfl]
    by_cases h : β l = 0
    · have hl : l ∉ β.support := by
        rw [Finsupp.mem_support_iff, not_not]
        exact h
      rw [coeff_X_mul', if_neg hl, h]
      simp
    · have hβ : β = Finsupp.single l 1 + (β - Finsupp.single l 1) := by
        ext i
        simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
        split_ifs with hli
        · subst hli
          omega
        · omega
      obtain ⟨γ, rfl⟩ : ∃ γ, β = Finsupp.single l 1 + γ := ⟨_, hβ⟩
      rw [add_tsub_cancel_left, coeff_X_mul, wt_single_add, Finsupp.add_apply,
        Finsupp.single_eq_same]
      push_cast
      ring
  · rw [map_add, fockInner_add_right, fockInner_add_right, h₁, h₂]
end FockRaiseLowInner
