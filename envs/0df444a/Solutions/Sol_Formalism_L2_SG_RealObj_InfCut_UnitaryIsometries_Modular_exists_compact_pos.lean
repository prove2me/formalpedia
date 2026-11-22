-- Prove2me | solution 1 for Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular.exists_compact_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:24:30.183518+00:00
-- url     : https://prove2.me/submissions/84e72143-4e1e-440f-8730-678e621569cb

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
theorem _root_.solution : ∃ C : Set G, IsCompact C ∧ 0 < (Measure.haar : Measure G) C ∧
    (Measure.haar : Measure G) C ≠ ⊤ := by
  obtain ⟨C, hC, h1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨C, hC, ?_, hC.measure_lt_top.ne⟩
  exact Measure.measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 h1⟩
end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
