-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.plOver_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:32.260519+00:00
-- url     : https://prove2.me/submissions/d055ffaf-6340-4098-ad86-0f58820a0228

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_P2M_Formalism_DivisionValues_PlaceSumConjugation_natCast_ne_zero__72e1bc708076

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Finset
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.PlaceSumConjugation
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.DivisionValues.PlaceSumConjugation
theorem _root_.solution (g : ℕ) : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite := by
  rcases Nat.eq_zero_or_pos g with hg | hg
  · subst hg
    convert Set.finite_empty
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    unfold PlOver vw
    first | simp [FractionalIdeal.count_zero] | (unfold FractionalIdeal.count; simp)
  · have hI : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g : K) ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact natCast_ne_zero' hg
    have hfin := FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g : K))
    have hsub : {w : HeightOneSpectrum (𝓞 K) | PlOver g w} ⊆ {v | FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (g : K)) ≠ 0} := by
      intro w hw
      simp only [Set.mem_setOf_eq] at hw ⊢
      unfold PlOver vw at hw
      exact hw.ne'
    first | exact (Filter.eventually_cofinite.mp hfin).subset hsub | exact hfin.subset hsub
end Formalism.DivisionValues.PlaceSumConjugation
