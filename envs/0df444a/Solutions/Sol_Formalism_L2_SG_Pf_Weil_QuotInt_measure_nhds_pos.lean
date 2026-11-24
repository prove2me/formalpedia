-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.measure_nhds_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:40.251951+00:00
-- url     : https://prove2.me/submissions/59d907d6-7e88-4407-9480-bef071a93439

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
theorem _root_.solution (κ : Measure H) [IsOpenPosMeasure κ] {V : Set G} (hV : V ∈ 𝓝 (1 : G)) :
    0 < κ {h : H | (h : G) ∈ V} := by
  have h1 : ((↑) : H → G) ⁻¹' V ∈ 𝓝 (1 : H) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hV
  first
  | exact measure_pos_of_mem_nhds κ h1
  | exact (measure_pos_of_nonempty_interior κ ⟨1, mem_interior_iff_mem_nhds.2 h1⟩)
end Formalism.L2.SG.Pf.Weil.QuotInt
