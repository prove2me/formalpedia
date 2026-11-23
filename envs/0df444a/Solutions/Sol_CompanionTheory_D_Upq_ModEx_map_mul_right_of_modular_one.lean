-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.map_mul_right_of_modular_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:06.119847+00:00
-- url     : https://prove2.me/submissions/29e08fdc-1a77-4f6a-9fbb-9dcc8afbc5f4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_map_mul_right_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix TopologicalSpace
open scoped ENNReal NNReal Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.ModEx
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
namespace CompanionTheory.D.Upq.ModEx
theorem _root_.solution (h1 : ∀ g : H, modularCharacterFun g = 1)
    (ν : Measure H) [SigmaFinite ν] [IsMulLeftInvariant ν] (g : H) : map (· * g) ν = ν := by
  have K : PositiveCompacts H := Classical.arbitrary _
  have h := haarMeasure_unique ν K
  have h2 : map (· * g) (haarMeasure K) = haarMeasure K := by
    rw [map_mul_right_eq (haarMeasure K) g, h1 g, one_smul]
  calc map (· * g) ν = map (· * g) (ν K • haarMeasure K) := by rw [← h]
    _ = ν K • haarMeasure K := by rw [Measure.map_smul, h2]
    _ = ν := h.symm
end CompanionTheory.D.Upq.ModEx
