-- Prove2me | solution 1 for Formalism.DivisionValues.good_twisted_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:45.124106+00:00
-- url     : https://prove2.me/submissions/54b99dd5-94c5-4415-960a-b1df64cc5173

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ScalarLiftLowerBoundFull
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AuxStatement14
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_WeightedPlaceLogSum
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_GlobalBoundRefinements
import Theorems.Thm_Formalism_DivisionValues_DivisorInequalityBounds_image_eq
import Theorems.Thm_Formalism_DivisionValues_DivisorInequalityBounds_goodFull
import Theorems.Thm_Formalism_DivisionValues_WeightedPlaceLogSum
import Theorems.Thm_Formalism_DivisionValues_eigen_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.DivisionValues
open DivisorInequalityBounds
namespace Formalism.DivisionValues
theorem _root_.solution : GoodTwist := by
  intro K _ _ _ K0 hK0 v0 hv0 n H hH hpos 𝒯 h0 hc ha e he0 hee hec hea Z Ω _ j S hZ σ
  exact eigen_twist K K0 hK0 v0 hv0 n H hH hpos (𝒯 ∪ {e})
    (by
      rintro T (hT | hT)
      · exact h0 T hT
      · rw [Set.mem_singleton_iff.mp hT]; exact he0)
    (by
      rintro T (hT | hT) T' (hT' | hT')
      · exact hc T hT T' hT'
      · rw [Set.mem_singleton_iff.mp hT']; exact (hec T hT).symm
      · rw [Set.mem_singleton_iff.mp hT]; exact hec T' hT'
      · rw [Set.mem_singleton_iff.mp hT, Set.mem_singleton_iff.mp hT'])
    (by
      rintro T (hT | hT)
      · obtain ⟨T', hT', h⟩ := ha T hT
        exact ⟨T', Or.inl hT', h⟩
      · rw [Set.mem_singleton_iff.mp hT]; exact ⟨e, Or.inr rfl, hea⟩)
    Z Ω j
    (by
      apply goodFull j 𝒯 e Z S
      rw [hZ]
      simp only [image_eq j 𝒯 e hee hec]) σ
end Formalism.DivisionValues
