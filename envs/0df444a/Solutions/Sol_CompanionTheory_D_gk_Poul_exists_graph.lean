-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.exists_graph
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:24.460565+00:00
-- url     : https://prove2.me/submissions/18b30086-d9b5-4c46-9011-ed88fdfd160f

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Theorems.Thm_CompanionTheory_D_gk_Poul_inner_map_left
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_inner_map_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.Poul
variable {G : Type} [Group G] {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  {σ : G →* (H →L[ℂ] H)} {σ' : G →* (H' →L[ℂ] H')}
namespace CompanionTheory.D.gk.Poul
theorem _root_.solution (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hiso' : ∀ g v, ‖σ' g v‖ = ‖v‖)
    (hs : ∀ T : H' →L[ℂ] H', (∀ g v, T (σ' g v) = σ' g (T v)) → ∃ c : ℂ, ∀ v, T v = c • v)
    (Γ : Submodule ℂ (H' × H)) (hcl : IsClosed (Γ : Set (H' × H))) (hinv : ∀ g, ∀ p ∈ Γ, (σ' g p.1, σ g p.2) ∈ Γ)
    {y₀ : H'} {z₀ : H} (h₀ : (y₀, z₀) ∈ Γ) (hy₀ : y₀ ≠ 0) :
    ∃ T : H' →L[ℂ] H, (∀ g y, T (σ' g y) = σ g (T y)) ∧ ∀ y, (y, T y) ∈ Γ := by
  let e : WithLp 2 (H' × H) ≃L[ℂ] H' × H := WithLp.prodContinuousLinearEquiv 2 ℂ H' H
  let V : Submodule ℂ (WithLp 2 (H' × H)) := Γ.comap (e : WithLp 2 (H' × H) →ₗ[ℂ] H' × H)
  have hV : IsClosed (V : Set (WithLp 2 (H' × H))) := hcl.preimage e.continuous
  have : CompleteSpace V := hV.completeSpace_coe
  let U : G → H' × H → WithLp 2 (H' × H) := fun g p => e.symm (σ' g p.1, σ g p.2)
  have hQ : ∀ g (p : H' × H), V.starProjection (U g p) = U g (e (V.starProjection (e.symm p))) := by
    intro g p
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw => ?_
    · exact hinv g _ (V.starProjection_apply_mem (e.symm p))
    · have h1 := V.starProjection_inner_eq_zero (e.symm p) (U g⁻¹ (e w)) (hinv g⁻¹ _ hw)
      rw [← h1, WithLp.prod_inner_apply, WithLp.prod_inner_apply]
      show ⟪σ' g p.1 - σ' g _, _⟫_ℂ + ⟪σ g p.2 - σ g _, _⟫_ℂ = _
      rw [← map_sub, ← map_sub, inner_map_left hiso', inner_map_left hiso]
      rfl
  let Q : H' →L[ℂ] H' × H :=
    (e : WithLp 2 (H' × H) →L[ℂ] H' × H) ∘L V.starProjection ∘L (e.symm : H' × H →L[ℂ] WithLp 2 (H' × H)) ∘L
      ContinuousLinearMap.inl ℂ H' H
  have hQa : ∀ y, Q y = e (V.starProjection (e.symm (y, 0))) := fun y => rfl
  have hQg : ∀ g y, Q (σ' g y) = (σ' g (Q y).1, σ g (Q y).2) := by
    intro g y
    have := hQ g (y, 0)
    simp only [U, map_zero] at this
    rw [hQa, this]
    rfl
  have hQm : ∀ y, Q y ∈ Γ := fun y => V.starProjection_apply_mem _
  obtain ⟨c, hc⟩ := hs (ContinuousLinearMap.fst ℂ H' H ∘L Q) fun g v => congrArg Prod.fst (hQg g v)
  have hc' : ∀ y, (Q y).1 = c • y := hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    set q := V.starProjection (e.symm (y₀, 0)) with hq
    have h1 := V.starProjection_inner_eq_zero (e.symm (y₀, 0)) q (V.starProjection_apply_mem _)
    have h2 := V.starProjection_inner_eq_zero (e.symm (y₀, 0)) (e.symm (y₀, z₀)) h₀
    rw [← hq, inner_sub_left] at h1 h2
    have h3 : ⟪e.symm (y₀, 0), q⟫_ℂ = 0 := by
      rw [WithLp.prod_inner_apply]
      show ⟪y₀, (Q y₀).1⟫_ℂ + ⟪(0 : H), _⟫_ℂ = 0
      rw [hc']; simp
    rw [h3, zero_sub, neg_eq_zero, inner_self_eq_zero] at h1
    rw [h1, inner_zero_left, sub_zero, WithLp.prod_inner_apply] at h2
    have h4 : ⟪y₀, y₀⟫_ℂ + ⟪(0 : H), z₀⟫_ℂ = 0 := h2
    rw [inner_zero_left, add_zero, inner_self_eq_zero] at h4
    exact hy₀ h4
  refine ⟨c⁻¹ • (ContinuousLinearMap.snd ℂ H' H ∘L Q), fun g y => ?_, fun y => ?_⟩
  · show c⁻¹ • (Q (σ' g y)).2 = σ g (c⁻¹ • (Q y).2)
    rw [hQg, map_smul]
  · have := Γ.smul_mem c⁻¹ (hQm y)
    convert this using 1
    refine Prod.ext ?_ rfl
    show y = c⁻¹ • (Q y).1
    rw [hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
end CompanionTheory.D.gk.Poul
