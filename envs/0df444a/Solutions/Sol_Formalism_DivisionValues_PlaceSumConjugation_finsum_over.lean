-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.finsum_over
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:00:23.528396+00:00
-- url     : https://prove2.me/submissions/d583fd8b-354d-421a-a6fb-4596fb0f4063

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds

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
theorem _root_.solution {g : ℕ} (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ᶠ (w : HeightOneSpectrum (𝓞 K)) (_ : PlOver g w), f w = ∑ w ∈ hS.toFinset, f w := by
  exact finsum_mem_eq_finite_toFinset_sum f hS
end Formalism.DivisionValues.PlaceSumConjugation
