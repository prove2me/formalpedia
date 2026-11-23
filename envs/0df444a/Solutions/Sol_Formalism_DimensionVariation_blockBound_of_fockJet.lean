-- Prove2me | solution 1 for Formalism.DimensionVariation.blockBound_of_fockJet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:37.427066+00:00
-- url     : https://prove2.me/submissions/2255e3b2-c69d-4425-9fd9-99a96d7a5542

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_BlockIntegralOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_HeightsoundOf
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GaussCoord
import Theorems.Thm_Formalism_DimensionVariation_blockIntegralBound
import Theorems.Thm_Formalism_DimensionVariation_blockBound_of


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
theorem _root_.solution (hF : FockJet) : BlockBound :=
  blockBound_of hF blockIntegralBound
end Formalism.DimensionVariation
