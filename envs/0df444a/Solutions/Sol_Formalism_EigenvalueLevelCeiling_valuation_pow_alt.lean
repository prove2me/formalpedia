-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.valuation_pow_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:15.036953+00:00
-- url     : https://prove2.me/submissions/bc8f1cbd-21de-476a-a098-59c641636fe2

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (a : K) (ha : a ≠ 0) (n : ℕ) : vw w (a ^ n) = (n : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
end Formalism.EigenvalueLevelCeiling
