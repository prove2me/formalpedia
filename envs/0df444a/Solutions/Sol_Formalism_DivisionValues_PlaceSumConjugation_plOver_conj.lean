-- Prove2me | solution 1 for Formalism.DivisionValues.PlaceSumConjugation.plOver_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:04.329967+00:00
-- url     : https://prove2.me/submissions/9bf94db1-862c-4e9a-9fe0-68e38bd1248a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Complement2Normaliser
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondComplementParameterBounds
import Theorems.Thm_Formalism_DivisionValues_PlaceSumConjugation_vw_conj_nat

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
theorem _root_.solution (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : PlOver g (conjPl w) ↔ PlOver g w := by
  unfold PlOver
  rw [vw_conj_nat]
end Formalism.DivisionValues.PlaceSumConjugation
