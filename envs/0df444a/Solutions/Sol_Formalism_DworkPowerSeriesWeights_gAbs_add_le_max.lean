-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.gAbs_add_le_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:46.536055+00:00
-- url     : https://prove2.me/submissions/bad456c8-da1b-4e98-b1fe-b1cf81e3d0d1

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
theorem _root_.solution (x y : GK F σ) : gAbs F σ (x + y) ≤ max (gAbs F σ x) (gAbs F σ y) := by
  have h := (gValK F σ).map_add x y
  rw [← NNReal.coe_le_coe, NNReal.coe_max] at h
  exact h
end Formalism.DworkPowerSeriesWeights
