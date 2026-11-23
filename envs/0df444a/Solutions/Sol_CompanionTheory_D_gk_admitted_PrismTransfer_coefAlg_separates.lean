-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.coefAlg_separates
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:06.460603+00:00
-- url     : https://prove2.me/submissions/2d5d97f0-f4d1-4aeb-95f9-65874f3250bd

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
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
variable {G : Type} [Group G] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
variable [TopologicalSpace G] {st : G → G} {S : Set G} {ρ : G →* Matrix ι ι ℂ} {ρ' : G →* Matrix ι' ι' ℂ}
namespace CompanionTheory.D.gk.admitted.PrismTransfer
theorem _root_.solution (h : IsGood st S ρ) (hi : Function.Injective ρ) (C : Set G) :
    (coefAlg st S C).SeparatesPoints := by
  intro x y hxy
  have : ρ x ≠ ρ y := fun e => hxy (Subtype.ext (hi e))
  obtain ⟨i, j, hij⟩ : ∃ i j, ρ x i j ≠ ρ y i j := by
    by_contra hc
    push Not at hc
    exact this (Matrix.ext hc)
  refine ⟨fun z : C => ρ z i j, ⟨⟨fun z : C => ρ z i j,
    (h.cont.matrix_elem i j).comp continuous_subtype_val⟩, ?_, rfl⟩, hij⟩
  refine ⟨ι, inferInstance, inferInstance, ρ, Pi.single i 1, Pi.single j 1, h, fun z => ?_⟩
  simp
end CompanionTheory.D.gk.admitted.PrismTransfer
