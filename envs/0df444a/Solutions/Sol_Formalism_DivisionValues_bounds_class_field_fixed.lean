-- Prove2me | solution 1 for Formalism.DivisionValues.bounds_class_field_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:42:33.089891+00:00
-- url     : https://prove2.me/submissions/ac8b905b-6d4d-4390-b320-f15d8be4f5d6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ClassSumDualGeF
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_valLatF_mono
import Theorems.Thm_Formalism_DivisionValues_class_sum_dual_le_fixed
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_valLatF_isLattice
import Theorems.Thm_Formalism_DivisionValues_divisor_bounds_first
import Theorems.Thm_Formalism_DivisionValues_projection_integral


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
theorem _root_.solution : BoundsIClassF := by
  intro K _ _ _ n' n H' hH hdet E Pr hO Cl _ V _ _ _ _ _ pair hs hn Gam _ _ ρ hiso I hinj hI hCS
    Nab Del hNab s hDel hle hstab G0 _ r c G he hc hr
  have hA := valLatF_isLattice I hinj Nab hNab
  have h1 := class_sum_dual_le_fixed K n' H' Cl V pair hs hn Gam ρ hiso I hI hCS Nab Del hNab s hDel hstab
  have h2 : valLatF I Del ≤ valLatF I Nab := valLatF_mono I hle
  have h3 := projection_integral K n' G0 r c G hc (valLatF I Del) hr
  rw [← he] at h3
  exact ⟨hA, divisor_bounds_first K n' n H' hH hdet E Pr hO _ _ hA s h1 G fun x hx => h2 (h3 x hx)⟩
end Formalism.DivisionValues
