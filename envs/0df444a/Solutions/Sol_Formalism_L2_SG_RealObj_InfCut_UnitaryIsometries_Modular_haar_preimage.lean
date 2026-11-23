-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.haar_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:09.834933+00:00
-- url     : https://prove2.me/submissions/7ce88e8f-317d-4281-b98d-2a4281c7fb67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EqOneOfZpowMem
import Theorems.Thm_Formalism_L2_SG_RealObj_InfCut_UnitaryIsometries_Modular_map_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal NNReal Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
local notation "Δ" => Measure.modularCharacterFun (G := G)
namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
theorem _root_.solution (g : G) {A : Set G} (hA : MeasurableSet A) :
    (Measure.haar : Measure G) ((· * g) ⁻¹' A) = (Δ g : ℝ≥0∞) * (Measure.haar : Measure G) A := by
  have h : ((Measure.haar : Measure G).map (· * g)) A = (Δ g • (Measure.haar : Measure G)) A := by rw [map_right]
  rw [Measure.map_apply (measurable_mul_const g) hA] at h
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
