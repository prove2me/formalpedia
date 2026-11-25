-- Prove2me | solution 1 for CompanionTheory.D.Upq.Quot.exists_isHaarOnM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:24:50.80015+00:00
-- url     : https://prove2.me/submissions/68aff3cd-4c15-46b5-bc57-8af5b320e68a

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_QuotientMeasureUnitaryGroup
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SigmaFiniteQuotients_ExistsQuotientMeasureUnitaryGroup
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_MG_measurableEmbedding_toM
import Theorems.Thm_CompanionTheory_D_Upq_ModEx_measurable_lmulQ


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
theorem _root_.solution {G : Set (Matrix (Fin m) (Fin m) ℂ)} (hG : IsMatGroup G) :
    ∃ μ : Measure (MtM m), IsHaarOnM G μ := by
  have hι := MG.measurableEmbedding_toM (hG := hG)
  let μ : Measure (MG G hG) := haar
  refine ⟨μ.map MG.toM, hι.sigmaFinite_map, ?_, ?_, fun s hs => ?_⟩
  · rw [Ne, Measure.map_eq_zero_iff hι.measurable.aemeasurable]
    exact NeZero.ne μ
  · rw [hι.map_apply]
    have : (MG.toM : MG G hG → MtM m) ⁻¹' {x | Matrix.of x ∉ G} = ∅ :=
      Set.eq_empty_of_forall_notMem fun a ha => ha a.mem
    rw [this, measure_empty]
  · have e : lmulQ s ∘ MG.toM = MG.toM ∘ (fun x : MG G hG => MG.mk hG s hs * x) := rfl
    rw [map_map (measurable_lmulQ _) hι.measurable, e,
      ← map_map hι.measurable (measurable_const_mul _), map_mul_left_eq_self]
end CompanionTheory.D.Upq.Quot
