-- Prove2me | solution 1 for Formalism.DivisionValues.ReductionFirst.cO_mem_Tw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:29.434071+00:00
-- url     : https://prove2.me/submissions/480156c2-fe98-413c-9b4c-5f9e57193a3c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SelectionLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionLemmaFirst
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_cO_cO

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
theorem _root_.solution {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : cO K s ∈ Tw w :=
  ⟨hs.2, by rw [cO_cO]; exact hs.1⟩
end Formalism.DivisionValues.ReductionFirst
