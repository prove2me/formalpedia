-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.exists_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:01.010797+00:00
-- url     : https://prove2.me/submissions/5216b660-1af8-4359-aa6b-457ae2fe2860

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_norm_avg_le
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
theorem _root_.solution [SecondCountableTopology K] (he : Continuous e) (l : List G) :
    ∀ C : Set G, IsCompact C → ∃ C' : Set G, IsCompact C' ∧ ∀ Φ F, IsFam μ e Φ F → ∀ δ : ℝ,
      (∀ y ∈ C', ‖Φ y‖ ≤ δ) → ∀ x ∈ C, ‖F l x‖ ≤ (∫ k, ‖e k‖ ∂μ) ^ (l.length + 1) * δ := by
  have hK : IsCompact (K : Set G) := isCompact_iff_compactSpace.2 ‹_›
  induction l with
  | nil =>
    intro C hC
    refine ⟨C * (K : Set G), hC.mul hK, fun Φ F h δ hδ x hx => ?_⟩
    rw [h.nil]
    simpa using norm_avg_le (μ := μ) he fun k => hδ _ (Set.mul_mem_mul hx k.2)
  | cons a l ih =>
    intro C hC
    obtain ⟨C', hC', H⟩ := ih (C * (K : Set G) * {a}) ((hC.mul hK).mul isCompact_singleton)
    refine ⟨C', hC', fun Φ F h δ hδ x hx => ?_⟩
    rw [h.cons, List.length_cons, pow_succ', mul_assoc]
    exact norm_avg_le he fun k => H Φ F h δ hδ _ (Set.mul_mem_mul (Set.mul_mem_mul hx k.2) rfl)
end CompanionTheory.D.gk.admitted.PrismTransfer
