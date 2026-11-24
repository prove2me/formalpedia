-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.measurable_mulH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:37.325435+00:00
-- url     : https://prove2.me/submissions/e58a6d0a-8829-4190-b7a1-5c48bcec5df3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Set Filter
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Weil
open Formalism.L2.SG.Pf.Weil.QuotInt
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] {H : Subgroup G}
namespace Formalism.L2.SG.Pf.Weil.QuotInt
theorem _root_.solution : Measurable (fun p : G × H => p.1 * (p.2 : G)) := by
  exact measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)
end Formalism.L2.SG.Pf.Weil.QuotInt
