-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.IsFam.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:47.000477+00:00
-- url     : https://prove2.me/submissions/7b3f36a8-2cd6-47a8-bb48-d894369c7072

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
namespace CompanionTheory.D.gk.admitted.PrismTransfer
namespace IsFam
theorem _root_.solution [SecondCountableTopology K] (he : Continuous e) {Φ Φ' : G → ℂ} {F F' : List G → G → ℂ}
    (h : IsFam μ e Φ F) (h' : IsFam μ e Φ' F') :
    IsFam μ e (fun x => Φ x - Φ' x) (fun l x => F l x - F' l x) where
  cont₀ := h.cont₀.sub h'.cont₀
  cont l := (h.cont l).sub (h'.cont l)
  nil x := by
    have h1 := h.cont₀
    have h2 := h'.cont₀
    rw [h.nil, h'.nil, ← integral_sub (integrable_of_cont (by fun_prop)) (integrable_of_cont (by fun_prop))]
    simp only [mul_sub]
  cons a l x := by
    have h1 := h.cont l
    have h2 := h'.cont l
    rw [h.cons, h'.cons, ← integral_sub (integrable_of_cont (by fun_prop)) (integrable_of_cont (by fun_prop))]
    simp only [mul_sub]
end IsFam
end CompanionTheory.D.gk.admitted.PrismTransfer
