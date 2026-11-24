-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DiscFubiniVolume.vol_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:17:03.596932+00:00
-- url     : https://prove2.me/submissions/29d3cb34-a488-4895-974f-fd74b5e79284

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousOnG2SymmetricInterval
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscMeanValue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Metric
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DiscFubiniVolume
namespace Formalism.FourierDecayAlt.P.DiscFubiniVolume
theorem _root_.solution (s : ℝ) : volume {b : ℝ | b ^ 2 < s} = ENNReal.ofReal (2 * Real.sqrt s) := by
  have hset : {b : ℝ | b ^ 2 < s} = Ioo (-Real.sqrt s) (Real.sqrt s) := by
    ext b
    simp only [mem_setOf_eq, mem_Ioo]
    exact Real.sq_lt
  rw [hset, Real.volume_Ioo]
  congr 1
  ring
end Formalism.FourierDecayAlt.P.DiscFubiniVolume
