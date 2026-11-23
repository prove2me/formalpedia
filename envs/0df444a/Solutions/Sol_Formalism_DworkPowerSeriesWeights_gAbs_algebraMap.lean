-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.gAbs_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:31.324664+00:00
-- url     : https://prove2.me/submissions/611c2288-d0a2-428f-ab53-182831a934c0

import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_gValK_algebraMap

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
theorem _root_.solution (P : MvPolynomial σ F) : gAbs F σ (algebraMap _ (GK F σ) P) = gN P :=
  gValK_algebraMap P
end Formalism.DworkPowerSeriesWeights
