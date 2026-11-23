-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.vw_conj_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:37.770493+00:00
-- url     : https://prove2.me/submissions/335f9028-20f6-4e37-95ec-b87d219dfc46

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_star


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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.PlaceSumConjugation
theorem _root_.solution (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    vw (conjPl w) (g : K) = vw w (g : K) := by
  rw [← ValuationRepresentative.vw_star, star_natCast]
end Formalism.DivisionValues.PlaceSumConjugation
