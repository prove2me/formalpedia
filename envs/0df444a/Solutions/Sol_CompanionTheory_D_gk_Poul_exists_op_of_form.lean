-- Prove2me | solution 1 for CompanionTheory.D.gk.Poul.exists_op_of_form
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:48.380938+00:00
-- url     : https://prove2.me/submissions/ea68b324-0dd9-4f8e-9405-c2ecea1b9f94

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsOpOfForm
import Theorems.Thm_CompanionTheory_D_gk_Poul_inner_map_left
import Theorems.Thm_CompanionTheory_D_gk_Poul_exists_graph
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
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
    (S : Set H) (S' : Set H') (hS : ∀ g, ∀ x ∈ S, σ g x ∈ S) (hS' : ∀ g, ∀ y ∈ S', σ' g y ∈ S') (B : H → H' → ℂ)
    (hB : ∀ g, ∀ x ∈ S, ∀ y ∈ S', B (σ g x) (σ' g y) = B x y) {y₀ : H'} {z₀ : H} (hy₀S : y₀ ∈ S') (hy₀ : y₀ ≠ 0)
    (h₀ : ∀ x ∈ S, B x y₀ = ⟪z₀, x⟫_ℂ) :
    ∃ T : H' →L[ℂ] H, (∀ g y, T (σ' g y) = σ g (T y)) ∧
      ∀ x ∈ S, ∀ w, (∀ y ∈ S', B x y = ⟪y, w⟫_ℂ) → ∀ y ∈ S', B x y = ⟪T y, x⟫_ℂ := by
  let Γ : Submodule ℂ (H' × H) :=
    { carrier := {p | ∀ x ∈ S, ∀ w, (∀ y ∈ S', B x y = ⟪y, w⟫_ℂ) → ⟪p.2, x⟫_ℂ = ⟪p.1, w⟫_ℂ}
      add_mem' := fun {p q} hp hq x hx w hw => by
        simp only [Prod.snd_add, Prod.fst_add, inner_add_left, hp x hx w hw, hq x hx w hw]
      zero_mem' := fun x _ w _ => by simp
      smul_mem' := fun c p hp x hx w hw => by
        simp only [Prod.smul_snd, Prod.smul_fst, inner_smul_left, hp x hx w hw] }
  have hcl : IsClosed (Γ : Set (H' × H)) := by
    have : (Γ : Set (H' × H)) = ⋂ x ∈ S, ⋂ w, ⋂ _ : (∀ y ∈ S', B x y = ⟪y, w⟫_ℂ),
        {p : H' × H | ⟪p.2, x⟫_ℂ = ⟪p.1, w⟫_ℂ} := by
      ext p; simp [Γ]
    rw [this]
    exact isClosed_biInter fun x _ => isClosed_iInter fun w => isClosed_iInter fun _ =>
      isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hinv : ∀ g, ∀ p ∈ Γ, (σ' g p.1, σ g p.2) ∈ Γ := by
    intro g p hp x hx w hw
    show ⟪σ g p.2, x⟫_ℂ = ⟪σ' g p.1, w⟫_ℂ
    rw [inner_map_left hiso, inner_map_left hiso']
    refine hp _ (hS _ x hx) _ fun y hy => ?_
    rw [← hB g _ (hS _ x hx) y hy, ← inner_map_left hiso', ← hw _ (hS' g y hy), ← ContinuousLinearMap.mul_apply,
      ← map_mul, mul_inv_cancel, map_one]
    rfl
  obtain ⟨T, hT, hΓ⟩ := exists_graph hiso hiso' hs Γ hcl hinv (y₀ := y₀) (z₀ := z₀)
    (fun x hx w hw => (h₀ x hx).symm.trans (hw y₀ hy₀S)) hy₀
  exact ⟨T, hT, fun x hx w hw y hy => (hw y hy).trans (hΓ y x hx w hw).symm⟩
end CompanionTheory.D.gk.Poul
