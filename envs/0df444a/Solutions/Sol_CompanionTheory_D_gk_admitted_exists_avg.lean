-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.exists_avg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:54.605432+00:00
-- url     : https://prove2.me/submissions/fe2ed05f-4f92-4eb3-9dd7-723a3be3c3a6

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_ExistsAvg
import Theorems.Thm_CompanionTheory_D_gk_admitted_integrable_cont
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {e : K → ℂ}
    (he : Continuous e) : ∃ E : H →L[ℂ] H, ∀ u, E u = ∫ k, e k • σ k u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ k, e k • σ k u ∂μ
      map_add' := fun u w => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_cont (he.smul (hc u))) (integrable_cont (he.smul (hc w)))
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _
end CompanionTheory.D.gk.admitted
