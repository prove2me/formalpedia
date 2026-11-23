-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.integral_mem_of_forall_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:54.796051+00:00
-- url     : https://prove2.me/submissions/34d12922-b27d-4b15-988d-ade256def3fb

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_GoodPI
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
open MeasureTheory Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
variable {ι : Type} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace CompanionTheory.D.gk.admitted
theorem _root_.solution {X : Type} [MeasurableSpace X] (μ : Measure X) (W : Submodule ℂ (ι → ℂ))
    (f : X → ι → ℂ) (hf : Integrable f μ) (hW : ∀ x, f x ∈ W) : ∫ x, f x ∂μ ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  have := (LinearMap.toContinuousLinearMap φ).integral_comp_comm hf
  simp only [LinearMap.coe_toContinuousLinearMap'] at this
  rw [← this]
  simp [fun x => hφ _ (hW x)]
end CompanionTheory.D.gk.admitted
