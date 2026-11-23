-- Prove2me | solution 1 for Formalism.DivisionValues.untwisted_choice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:18.483983+00:00
-- url     : https://prove2.me/submissions/99be27dd-95f9-456e-a0b0-906f722ff1e9

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares

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
namespace Formalism.DivisionValues
theorem _root_.solution : UntwistedChoice := by
  intro Pl J _ S Tw D hD hTS l ell I Ic jT F err Jx η hA hF h3 h4
  classical
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨fun w j => if w ∈ Tw then err w j else (I w j + Ic w j) / D,
    fun w j => if w ∈ Tw then Jx w j else jT w j / D,
    fun w j => if w ∈ Tw then η w j else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw j
    simp only [hw, if_true, and_self]
  · intro w hw
    by_cases hT : w ∈ Tw
    · simpa only [hT, if_true] using h3 w hT
    · simp only [hT, if_false]
      have e : ∑ j, (2 * F w j + (I w j + Ic w j) / D) = (∑ j, (I w j + Ic w j)) / D := by
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl (fun j _ => by rw [hF w hw hT j]; ring)
      rw [e, add_mul, div_mul_cancel₀ _ hD'.ne']
      have : 0 ≤ 2 / ell w ^ 2 * (D : ℝ) := by positivity
      linarith
  · intro w hw j
    by_cases hT : w ∈ Tw
    · simpa only [hT, if_true] using h4 w hT j
    · simp only [hT, if_false]
      rw [div_mul_cancel₀ _ hD'.ne', add_zero]
  · intro j
    rw [← Finset.sum_subset hTS (fun w hw hT => by
      simp only [hT, if_false]
      rw [← add_div, hA w hw hT j, zero_div, mul_zero])]
    exact Finset.sum_congr rfl (fun w hw => by simp only [hw, if_true])
  · intro j
    rw [← Finset.sum_subset hTS (fun w hw hT => by
      simp only [hT, if_false, mul_zero, zero_div])]
    exact Finset.sum_congr rfl (fun w hw => by simp only [hw, if_true])
  · intro j
    exact (Finset.sum_subset hTS (fun w hw hT => by rw [hF w hw hT j, mul_zero])).symm
end Formalism.DivisionValues
