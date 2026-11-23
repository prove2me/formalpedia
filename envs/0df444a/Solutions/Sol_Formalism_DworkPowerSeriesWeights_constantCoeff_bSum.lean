-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.constantCoeff_bSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:01:00.733983+00:00
-- url     : https://prove2.me/submissions/66fee6fa-a059-4cdd-a47f-fe4624ee62a3

import Definitions.Def_Formalism_GaussJetBounds_FrameJetEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_constantCoeff_linSub

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
theorem _root_.solution (M : ZV d N0 N1 → ι → K) (be : MvPowerSeries (ZMod d) K)
    (hbe : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (bSum M be) = 0 := by
  unfold bSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun ab _ => ?_
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => constantCoeff_linSub M _)
    (fun s => constantCoeff_linSub M _) hbe
end Formalism.DworkPowerSeriesWeights
