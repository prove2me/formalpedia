-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.map_linSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:04:36.695229+00:00
-- url     : https://prove2.me/submissions/d4e341a2-3386-491a-8afc-c3208b4360fe

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {F K : Type} [NormedField F] [CharZero F] [NormedField K] [CharZero K] (φ : F →+* K)
  {d N0 N1 : ℕ} [NeZero d] {ι : Type} [Fintype ι]
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (M : ZV d N0 N1 → ι → F) (z : ZV d N0 N1) :
    MvPowerSeries.map φ (linSub M z) = linSub (fun z i => φ (M z i)) z := by
  unfold linSub
  simp [map_sum]
end Formalism.DworkPowerSeriesWeights
