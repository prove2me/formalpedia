-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.translate_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:54.23785+00:00
-- url     : https://prove2.me/submissions/8b08bd5c-bb39-4493-b302-ae3039094f4c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTail
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsLower
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEquiv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μS : Measure G} {S : Set G} (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω)
    (hΩS : Ω ⊆ S) (hΩt : μS Ω < ⊤) {s : G} (hs : s ∈ S) :
    MeasurableSet ((fun v => v * s⁻¹) ⁻¹' Ω) ∧ (fun v => v * s⁻¹) ⁻¹' Ω ⊆ S ∧
      μS ((fun v => v * s⁻¹) ⁻¹' Ω) < ⊤ := by
  obtain ⟨-, -, hmul, hinv, -, -, -, -, -, hr, -⟩ := hS
  refine ⟨hΩm.preimage (measurable_mul_const s⁻¹), fun v hv => ?_, ?_⟩
  · have h1 : v * s⁻¹ * s ∈ S := hmul _ (@hΩS (v * s⁻¹) hv) _ hs
    simpa using h1
  · rw [← Measure.map_apply (measurable_mul_const s⁻¹) hΩm, hr _ (hinv _ hs)]
    exact hΩt
end Formalism.L2.S.Pv.EnergyAbs
