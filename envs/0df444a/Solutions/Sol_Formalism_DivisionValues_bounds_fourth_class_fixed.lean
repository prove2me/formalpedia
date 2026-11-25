-- Prove2me | solution 1 for Formalism.DivisionValues.bounds_fourth_class_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:47:20.549982+00:00
-- url     : https://prove2.me/submissions/cf360f41-9f17-4ec6-8245-c34cbf8c8d1f

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Theorems.Thm_Formalism_DivisionValues_class_sum_dual_ge_fixed
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_valLatF_isLattice
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_mul
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_mul
import Theorems.Thm_Formalism_DivisionValues_bounds_fourth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open exponent_index_lattice ValuationLatticeField
open ValuationLatticeField
namespace Formalism.DivisionValues
theorem _root_.solution : BoundsIVClassF := by
  intro K _ _ _ n d H hH hdet E Pr hO Cl _ V _ _ _ _ pair I g hinj hg hCS Nab Del hNab s hs0 hDel
    DG hDG hdvd w ϖ J hϖ hJ
  have hA := valLatF_isLattice I hinj Nab hNab
  have h1 := class_sum_dual_ge_fixed K n H Cl V pair I g hg hCS Nab Del s hDel DG hdvd
  have h := bounds_fourth K n d H hH hdet E Pr hO _ _ hA (DG * s) (Nat.mul_pos hDG hs0) h1 w ϖ J hϖ hJ
  have hG' : (DG : K) ≠ 0 := by exact_mod_cast hDG.ne'
  have hs' : (s : K) ≠ 0 := by exact_mod_cast hs0.ne'
  have h4 := h.2.2.2
  rw [Nat.cast_mul, ValuationRepresentative.vw_mul w _ _ hG' hs', ← add_assoc] at h4
  exact ⟨h.1, h4⟩
end Formalism.DivisionValues
