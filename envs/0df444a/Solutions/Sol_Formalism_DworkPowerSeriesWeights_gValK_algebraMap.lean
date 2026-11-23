-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.gValK_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:03.019439+00:00
-- url     : https://prove2.me/submissions/d019cc72-02bb-4df3-80d5-886457af98c8

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
variable {F : Type} [NormedField F] {σ : Type}
variable [IsUltrametricDist F]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (P : MvPolynomial σ F) :
    ((gValK F σ (algebraMap _ (GK F σ) P) : ℝ≥0) : ℝ) = gN P := by
  rw [gValK, Valuation.extendToLocalization_apply_map_apply, gVal_coe]
end Formalism.DworkPowerSeriesWeights
