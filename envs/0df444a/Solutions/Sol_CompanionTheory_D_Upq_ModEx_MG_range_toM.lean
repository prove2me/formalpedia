-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.MG.range_toM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:05.687721+00:00
-- url     : https://prove2.me/submissions/6efc41a3-e503-4e03-894a-284b53423763

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_ModExists

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
open PI PI.QuotSetU.UnitaryGroupMassFormula
variable {m : ℕ}
variable {G : Set (Matrix (Fin m) (Fin m) ℂ)} {hG : IsMatGroup G}
namespace CompanionTheory.D.Upq.ModEx
namespace MG
theorem _root_.solution : Set.range (MG.toM : MG G hG → MtM m) = {x | Matrix.of x ∈ G} := by
  ext x
  constructor
  · rintro ⟨a, rfl⟩; exact a.mem
  · intro hx; exact ⟨MG.mk hG (Matrix.of x) hx, rfl⟩
end MG
end CompanionTheory.D.Upq.ModEx
