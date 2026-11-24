-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Weil.QuotInt.measure_coset_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:38.226257+00:00
-- url     : https://prove2.me/submissions/11f16309-d1d2-469c-88c1-764fd3ac9392

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
theorem _root_.solution (κ : Measure H) [κ.IsMulLeftInvariant] (y : G) (E : Set G) :
    κ {h : H | y * h ∈ E} ≤ κ {h : H | (h : G) ∈ E⁻¹ * E} := by
  by_cases hne : ∃ h₀ : H, y * (h₀ : G) ∈ E
  · obtain ⟨h₀, hh₀⟩ := hne
    calc κ {h : H | y * h ∈ E}
        ≤ κ ((fun h : H => h₀⁻¹ * h) ⁻¹' {h : H | (h : G) ∈ E⁻¹ * E}) := by
          apply measure_mono
          intro h hh
          have hh' : y * (h : G) ∈ E := hh
          show ((h₀⁻¹ * h : H) : G) ∈ E⁻¹ * E
          rw [Set.mem_mul]
          refine ⟨(y * h₀)⁻¹, by rw [Set.mem_inv, inv_inv]; exact hh₀, y * h, hh', ?_⟩
          push_cast
          group
      _ = κ {h : H | (h : G) ∈ E⁻¹ * E} := measure_preimage_mul κ _ _
  · push_neg at hne
    have h0 : κ {h : H | y * h ∈ E} = 0 :=
      measure_mono_null (fun h hh => (hne h hh).elim) measure_empty
    rw [h0]
    first | exact zero_le _ | exact zero_le | simp
end Formalism.L2.SG.Pf.Weil.QuotInt
