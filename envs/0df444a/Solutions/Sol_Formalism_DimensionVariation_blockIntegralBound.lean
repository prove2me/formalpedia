-- Prove2me | solution 1 for Formalism.DimensionVariation.blockIntegralBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:23:14.059076+00:00
-- url     : https://prove2.me/submissions/5f29735b-0bf0-48e8-8a15-28c6d9b8ce8e

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord
import Theorems.Thm_Formalism_DimensionVariation_gaussianIntegralDiagonal
import Theorems.Thm_Formalism_DimensionVariation_blockIntegral_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory
open scoped ComplexConjugate Real
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution : BlockIntegral :=
  blockIntegral_of gaussianIntegralDiagonal
end Formalism.DimensionVariation
