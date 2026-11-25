-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.measurable_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:13:15.897009+00:00
-- url     : https://prove2.me/submissions/be3cd3ac-f311-4b24-a800-f3a139445e88

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
theorem _root_.solution : Measurable ((↑) : G → G ⧸ H) := by
  first | exact measurable_quotient_mk'' | exact measurable_quotient_mk' | exact fun s hs => hs
end Formalism.L2.SG.Pf.Weil.QuotInt
