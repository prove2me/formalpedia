-- Prove2me | solution 1 for Formalism.DimensionVariation.top_net
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:17.972959+00:00
-- url     : https://prove2.me/submissions/68b0439e-5f72-440c-a293-7d88b7c08d0f

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution : TopNet6 := by
  intro k m j p q' h1 h2 hp hq
  subst hp hq
  refine ⟨⟨by ring, abs_le.mpr ⟨by linarith, by linarith⟩⟩,
    ⟨by ring, abs_le.mpr ⟨by linarith, by linarith⟩⟩⟩
end Formalism.DimensionVariation
