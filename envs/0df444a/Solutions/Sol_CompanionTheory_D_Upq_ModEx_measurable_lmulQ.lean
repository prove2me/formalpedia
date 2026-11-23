-- Prove2me | solution 1 for CompanionTheory.D.Upq.ModEx.measurable_lmulQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:05.818726+00:00
-- url     : https://prove2.me/submissions/3af2ecaf-ad32-4198-946e-7dd03eb72424

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
theorem _root_.solution (a : (Matrix (Fin m) (Fin m) ℂ)) : Measurable (lmulQ a) :=
  Continuous.measurable (α := MtM m) (γ := MtM m)
    (Continuous.matrix_mul (A := fun _ : (Matrix (Fin m) (Fin m) ℂ) => a) (B := fun x : (Matrix (Fin m) (Fin m) ℂ) => x) continuous_const
      continuous_id)
end CompanionTheory.D.Upq.ModEx
