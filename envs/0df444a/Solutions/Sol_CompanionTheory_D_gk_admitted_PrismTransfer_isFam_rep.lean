-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.isFam_rep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:53.975049+00:00
-- url     : https://prove2.me/submissions/2b87a726-2234-44f0-81e6-2202e82ae56b

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_integrable_of_cont
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
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.PrismTransfer
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Subgroup G} [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ]
  (e : K → ℂ)
variable {μ e}
omit [IsTopologicalGroup G]
namespace CompanionTheory.D.gk.admitted.PrismTransfer
theorem _root_.solution [SecondCountableTopology K] (he : Continuous e) {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [CompleteSpace V] (τ : G →* Module.End ℂ V) (h1 : ∀ x, Continuous (τ x))
    (h2 : ∀ v, Continuous fun x => τ x v) (E : Module.End ℂ V) (hE : ∀ u, E u = ∫ k : K, e k • τ k u ∂μ)
    (ℓ : V →L[ℂ] ℂ) (u : V) :
    IsFam μ e (fun x => ℓ (τ x u)) (fun l x => ℓ (τ x (word E (l.map τ) u))) := by
  have key : ∀ x w, ℓ (τ x (E w)) = ∫ k : K, e k * ℓ (τ (x * k) w) ∂μ := by
    intro x w
    have hw := h2 w
    have := (ℓ.comp ⟨τ x, h1 x⟩).integral_comp_comm (μ := μ) (φ := fun k : K => e k • τ k w)
      (integrable_of_cont (he.smul (hw.comp continuous_subtype_val)))
    rw [hE]
    refine Eq.trans this.symm ?_
    simp
  refine ⟨ℓ.continuous.comp (h2 u), fun l => ℓ.continuous.comp (h2 _), fun x => key x u, fun a l x => ?_⟩
  simp only [List.map_cons, word_cons, Module.End.mul_apply]
  rw [key]
  simp
end CompanionTheory.D.gk.admitted.PrismTransfer
