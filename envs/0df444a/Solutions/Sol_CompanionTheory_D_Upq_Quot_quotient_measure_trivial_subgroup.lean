-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.quotient_measure_trivial_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:06:02.295831+00:00
-- url     : https://prove2.me/submissions/a25a6856-9c2a-4094-8c41-984151a7acbd

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_QuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Theorems.Thm_CompanionTheory_D_Upq_Quot_isMatGroup_one
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_measurable_lmulQ
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_measurable_rmulQ


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
    QuotientSetting G {1} μ (dirac (oneM m)) μ := by
  refine ⟨hG, isMatGroup_one, Set.singleton_subset_iff.2 hG.2.1, hμ,
    ⟨inferInstance, NeZero.ne _, ?_, fun s hs => ?_⟩, hr, fun s hs => ?_, fun f _ => ?_⟩
  · rw [dirac_apply]
    refine Set.indicator_of_notMem ?_ _
    intro h
    exact h rfl
  · rw [Set.mem_singleton_iff.1 hs, map_dirac' (measurable_lmulQ _)]
    congr 1
    exact Matrix.mul_one (1 : Matrix (Fin m) (Fin m) ℂ)
  · rw [Set.mem_singleton_iff.1 hs, map_dirac' (measurable_rmulQ _)]
    congr 1
    exact Matrix.mul_one (1 : Matrix (Fin m) (Fin m) ℂ)
  · congr 1
    ext x
    rw [lintegral_dirac]
    congr 1
    exact (Matrix.one_mul (Matrix.of x)).symm
end CompanionTheory.D.Upq.Quot
