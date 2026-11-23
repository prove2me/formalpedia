-- Prove2me | solution 1 for Formalism.DimensionVariation.fjW_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:17.426258+00:00
-- url     : https://prove2.me/submissions/31872505-df3c-4327-8789-f2d3f6dd5b51

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjMoment
import Theorems.Thm_Formalism_DimensionVariation_fjW_continuous
import Theorems.Thm_Formalism_DimensionVariation_fjW_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution (a b : ℕ) : Integrable (fjW a b) :=
  (fjMoment 1 one_pos (a + b)).1.mono'
    (fjW_continuous a b).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (fjW_norm a b z).le)
end Formalism.DimensionVariation
