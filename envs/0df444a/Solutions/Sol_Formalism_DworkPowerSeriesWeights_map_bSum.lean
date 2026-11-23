-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.map_bSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:35.493264+00:00
-- url     : https://prove2.me/submissions/c7657ca5-a0ea-4078-8ab2-c4b911ab82f9

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_linSub
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_map_linSub

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
theorem _root_.solution (M : ZV d N0 N1 → ι → F) (be : MvPowerSeries (ZMod d) F) :
    MvPowerSeries.map φ (bSum M be) = bSum (fun z i => φ (M z i)) (MvPowerSeries.map φ be) := by
  unfold bSum
  rw [map_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [MvPowerSeries.map_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => constantCoeff_linSub M _)]
  simp only [map_linSub]
end Formalism.DworkPowerSeriesWeights
