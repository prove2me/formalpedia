-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.PrismTransfer.exists_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:01.135633+00:00
-- url     : https://prove2.me/submissions/376fe52e-aa6d-432a-84c5-f385e5cbeeb7

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_Transfer
import Theorems.Thm_CompanionTheory_D_gk_admitted_PrismTransfer_coefAlg_separates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped Kronecker Pointwise
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.PrismTransfer
variable {G : Type} [Group G] {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
variable [TopologicalSpace G] {st : G → G} {S : Set G} {ρ : G →* Matrix ι ι ℂ} {ρ' : G →* Matrix ι' ι' ℂ}
namespace CompanionTheory.D.gk.admitted.PrismTransfer
theorem _root_.solution (h : IsGood st S ρ) (hi : Function.Injective ρ) {C : Set G} (hC : IsCompact C)
    {Φ : G → ℂ} (hΦ : Continuous Φ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (τ : G →* Matrix κ κ ℂ) (a b : κ → ℂ),
      IsGood st S τ ∧ ∀ x ∈ C, ‖Φ x - a ⬝ᵥ (τ x *ᵥ b)‖ ≤ δ := by
  have : CompactSpace C := isCompact_iff_compactSpace.1 hC
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (coefAlg_separates h hi C)
  let F : C(C, ℂ) := ⟨fun x => Φ x, hΦ.comp continuous_subtype_val⟩
  have hF : F ∈ closure (coefAlg st S C : Set C(C, ℂ)) := by
    have : F ∈ (coefAlg st S C).topologicalClosure := by rw [htop]; trivial
    exact this
  obtain ⟨f, ⟨κ, _, _, τ, a, b, hτ, hf⟩, hd⟩ := Metric.mem_closure_iff.1 hF δ hδ
  refine ⟨κ, inferInstance, inferInstance, τ, a, b, hτ, fun x hx => ?_⟩
  have := (ContinuousMap.dist_apply_le_dist (f := F) (g := f) ⟨x, hx⟩).trans hd.le
  rw [dist_eq_norm, hf] at this
  exact this
end CompanionTheory.D.gk.admitted.PrismTransfer
