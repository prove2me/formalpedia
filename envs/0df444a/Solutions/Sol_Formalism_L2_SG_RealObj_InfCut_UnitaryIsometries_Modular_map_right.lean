-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.map_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:32:45.78352+00:00
-- url     : https://prove2.me/submissions/9bf31e23-2c93-4ed9-9fad-c367d31b2fa2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EqOneOfZpowMem

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
theorem _root_.solution (g : G) : (Measure.haar : Measure G).map (· * g) = Δ g • (Measure.haar : Measure G) :=
  Measure.map_right_mul_eq_modularCharacterFun_smul _ g
end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
