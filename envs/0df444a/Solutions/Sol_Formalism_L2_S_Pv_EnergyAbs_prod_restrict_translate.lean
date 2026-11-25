-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.prod_restrict_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:18:08.428587+00:00
-- url     : https://prove2.me/submissions/70ec47d1-dec5-4063-8f4f-334a13f45685

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μS : Measure G} [SFinite μS] (ν : Measure G) [SFinite ν] {s0 : G}
    (hmap : μS.map (fun x => x * s0⁻¹) = μS) (A : Set G) :
    ν.prod (μS.restrict A) =
      (ν.prod (μS.restrict ((fun v => v * s0⁻¹) ⁻¹' A))).map (Prod.map id (fun v => v * s0⁻¹)) := by
  have hE := (MeasurableEquiv.mulRight (s0⁻¹ : G)).measurableEmbedding.restrict_map μS A
  rw [MeasurableEquiv.coe_mulRight, hmap] at hE
  rw [← Measure.map_prod_map ν _ measurable_id (measurable_mul_const s0⁻¹), Measure.map_id, ← hE]
end Formalism.L2.S.Pv.EnergyAbs
