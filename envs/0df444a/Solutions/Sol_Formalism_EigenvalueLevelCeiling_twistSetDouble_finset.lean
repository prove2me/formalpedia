-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.twistSetDouble_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:39:37.31669+00:00
-- url     : https://prove2.me/submissions/560163b9-1f30-434e-8bdc-35c71bfc5c0f

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_twist_set_double

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
open Classical
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (K : Type) [Field K] [NumberField K] [StarRing K] (J : Type) [Fintype J]
    (ε0 : HeightOneSpectrum (𝓞 K) → J → ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (h : ∀ w ∈ S, ∑ j, (ε0 w j + (if conjPl w = w then 0 else ε0 (conjPl w) j)) ≤ 1 / (plc w : ℝ) ^ 2) :
    ∀ w ∈ S, ∑ j, (ε0 w j + ε0 (conjPl w) j) ≤ 2 / (plc w : ℝ) ^ 2 := by
  intro w hw
  exact twist_set_double K J ε0 w (h w hw)
end Formalism.EigenvalueLevelCeiling
