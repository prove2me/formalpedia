-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmOne_smul_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:23.772771+00:00
-- url     : https://prove2.me/submissions/36507569-22fa-41d8-9337-4c4e12789c88

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne

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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [NormedField K] {ι : Type v} (c : K)
    {f : MvPowerSeries ι K} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (c • f) = 0 := by
  first
    | simp [hf]
    | rw [MvPowerSeries.smul_eq_C_mul, map_mul, hf, mul_zero]
end Formalism.DworkPowerSeriesWeights
