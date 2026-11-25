-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.measure_inv_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:01:15.326159+00:00
-- url     : https://prove2.me/submissions/c2963b6d-8b2d-4971-9015-13011675fb0b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsLower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Measure Filter Topology
open scoped ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μS : Measure G} [MeasurableInv G] (hinv : μS.map (fun x => x⁻¹) = μS)
    (B : Set G) : μS {s | s⁻¹ ∈ B} = μS B := by
  have e : (μS.map (MeasurableEquiv.inv G)) B = μS ((MeasurableEquiv.inv G) ⁻¹' B) :=
    MeasurableEquiv.map_apply _ _
  have hm : μS.map (MeasurableEquiv.inv G) = μS := hinv
  rw [hm] at e
  exact e.symm
end Formalism.L2.S.Pv.EnergyAbs
