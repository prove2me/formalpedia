-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.measurable_rmulQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:06.114491+00:00
-- url     : https://prove2.me/submissions/6ddd80f3-f136-417e-9eb3-602b7eebfa59

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
theorem _root_.solution (a : (Matrix (Fin m) (Fin m) ℂ)) : Measurable (rmulQ a) :=
  Continuous.measurable (α := MtM m) (γ := MtM m)
    (Continuous.matrix_mul (A := fun x : (Matrix (Fin m) (Fin m) ℂ) => x) (B := fun _ : (Matrix (Fin m) (Fin m) ℂ) => a) continuous_id
      continuous_const)
end CompanionTheory.D.Upq.ModEx
