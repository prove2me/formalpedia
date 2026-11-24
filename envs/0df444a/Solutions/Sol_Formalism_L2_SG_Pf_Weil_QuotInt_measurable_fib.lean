-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.measurable_fib
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:27:23.346792+00:00
-- url     : https://prove2.me/submissions/6d3fdf0e-dbda-4031-b955-828a8b867257

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CasimirReductionTheory_OneParameterDerivatives_WeilIndicatorMeasures_MeasurableUnitMulIndicator
import Theorems.Thm_Formalism_L2_SG_Pf_Weil_QuotInt_measurable_mulH

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
theorem _root_.solution (κ : Measure H) [SFinite κ] {f : G → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fib κ f) := by
  exact (hf.comp measurable_mulH).lintegral_prod_right'
end Formalism.L2.SG.Pf.Weil.QuotInt
