-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.vw_nat_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:44.390223+00:00
-- url     : https://prove2.me/submissions/7708208c-17f5-4dd6-a711-4e8937c44d3e

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
theorem _root_.solution (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ vw w (g : K) := by
  unfold vw
  have h : (g : K) = algebraMap (𝓞 K) K (g : 𝓞 K) := by simp
  rw [h, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg
end Formalism.DivisionValues.PlaceSumConjugation
