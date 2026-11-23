-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.lemmaSt_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:01:35.420054+00:00
-- url     : https://prove2.me/submissions/27972aad-b8e9-4587-8b4e-7279a5787cd9

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffEvenDerivativeEqZero
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPowerSeries
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u}) : LemmaSt.{u} := by
  intro K _ _ _ l d _ hl hpi g hg0 hgl x
  have hb := (hB K l d 0 0).1
  exact hG K l hl hpi (V2 d) (fun y => (y.1, y.2 - 2)) g hg0 (fun x => by rw [← hb x]; exact hgl x) x
end Formalism.DworkPowerSeriesWeights
