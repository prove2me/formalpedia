-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:36.687433+00:00
-- url     : https://prove2.me/submissions/aaa02c95-2c39-4987-8915-be6361528172

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_mem
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply


attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply

set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (L : ι → H →L[ℂ] H) (y : ι → H) (h : ∀ g, ∑ k, L k (σ g (y k)) = 0) (T : H →L[ℂ] H) :
    ∑ k, L k (T (y k)) = 0 := by
  let Λ : PiLp 2 (fun _ : ι => H) →L[ℂ] H := ∑ k, (L k).comp (PiLp.proj 2 (fun _ : ι => H) k)
  have hΛ : ∀ z, Λ z = ∑ k, L k (z k) := fun z => by simp [Λ]
  let C : Submodule ℂ (PiLp 2 (fun _ : ι => H)) :=
    ⨅ g : G, LinearMap.ker ((Λ.comp (diag (σ g)) : PiLp 2 (fun _ : ι => H) →L[ℂ] H) :
      PiLp 2 (fun _ : ι => H) →ₗ[ℂ] H)
  have hmem : ∀ z, z ∈ C ↔ ∀ g, ∑ k, L k (σ g (z k)) = 0 := by
    intro z
    simp [C, hΛ]
  have hcl : IsClosed (C : Set (PiLp 2 (fun _ : ι => H))) := by
    simp only [C, Submodule.coe_iInf]
    exact isClosed_iInter fun g => (Λ.comp (diag (σ g))).isClosed_ker
  have hC : ∀ g, ∀ z ∈ C, diag (σ g) z ∈ C := by
    intro g z hz
    rw [hmem] at hz ⊢
    intro g'
    simpa using hz (g' * g)
  have := (hmem _).mp (diag_mem σ hσ hirr C hcl hC T (WithLp.toLp 2 y) ((hmem _).mpr h)) 1
  simpa using this
end CompanionTheory.D.gk.admitted.FinOfPIAux
