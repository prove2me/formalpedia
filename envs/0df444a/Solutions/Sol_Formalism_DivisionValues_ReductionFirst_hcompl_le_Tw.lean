-- Prove2me | solution 1 for Formalism.DivisionValues.ReductionFirst.hcompl_le_Tw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:07:25.494339+00:00
-- url     : https://prove2.me/submissions/3c747851-62a8-4fc5-8178-ee6b1acad833

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.ReductionFirst
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.ReductionFirst
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ Tw w := by
  refine Submonoid.closure_le.2 ?_
  rintro s ⟨hs, hs'⟩
  exact ⟨hs, hs' (cO K s) rfl⟩
end Formalism.DivisionValues.ReductionFirst
