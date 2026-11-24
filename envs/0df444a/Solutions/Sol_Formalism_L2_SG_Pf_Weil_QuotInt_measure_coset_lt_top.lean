-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.measure_coset_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:39.126368+00:00
-- url     : https://prove2.me/submissions/531fc343-2e18-4f02-bb70-0b390848e4f8

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
theorem _root_.solution (hH : IsClosed (H : Set G)) (κ : Measure H)
    [IsFiniteMeasureOnCompacts κ] {E : Set G} (hE : IsCompact E) :
    κ {h : H | (h : G) ∈ E⁻¹ * E} < ∞ := by
  have hc : IsCompact (E⁻¹ * E) := hE.inv.mul hE
  have hc2 : IsCompact {h : H | (h : G) ∈ E⁻¹ * E} := by
    first
    | exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hc
    | exact hH.closedEmbedding_subtype_val.isCompact_preimage hc
    | (rw [Subtype.isCompact_iff]
       have e : ((↑) : H → G) '' {h : H | (h : G) ∈ E⁻¹ * E} = (E⁻¹ * E) ∩ (H : Set G) := by
         ext x
         simp
       rw [e]
       exact hc.inter_right hH)
  exact hc2.measure_lt_top
end Formalism.L2.SG.Pf.Weil.QuotInt
