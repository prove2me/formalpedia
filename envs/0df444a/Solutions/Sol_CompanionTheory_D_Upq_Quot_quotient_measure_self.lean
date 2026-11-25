-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.quotient_measure_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:24:19.010793+00:00
-- url     : https://prove2.me/submissions/dd6f85ae-0fb2-4cac-97ac-916a5ab5b0df

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_QuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Quot
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula CompanionTheory.D.Upq.ModEx
variable {m : ℕ}
namespace CompanionTheory.D.Upq.Quot
theorem _root_.solution {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G)
    {μ : Measure (MtM m)} (hμ : IsHaarOnM G μ) (hr : IsRightInvM G μ) :
    QuotientSetting G G μ μ (dirac (oneM m)) := by
  refine ⟨hG, hG, subset_rfl, hμ, hμ, hr, hr, fun f _ => ?_⟩
  rw [lintegral_dirac]
  congr 1
  ext s
  congr 1
  exact (Matrix.mul_one (Matrix.of s)).symm
end CompanionTheory.D.Upq.Quot
