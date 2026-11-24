-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.inner_ds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:05.539813+00:00
-- url     : https://prove2.me/submissions/7c778d3d-f205-4305-9474-e48019002938

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_hasDerivAt_ds
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
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
attribute [local simp] CompanionTheory.D.gk.admitted.FinOfPIAux.diag_apply
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.FinalFormK
open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}
variable {L : Mat n → Prop}
namespace CompanionTheory.D.gk.FinalFormK
theorem _root_.solution (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) {u v : H} (hu : IsSm G σ u)
    (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G) : ⟪u, ds σ X v⟫_ℂ = ⟪-ds σ X u, v⟫_ℂ := by
  have h1 := (hasDerivAt_ds hσ hu hX).inner ℂ (hasDerivAt_ds hσ hv hX)
  have e : (fun t => ⟪σ (ex X t) u, σ (ex X t) v⟫_ℂ) = fun _ => ⟪u, v⟫_ℂ := funext fun t =>
    (⟨(σ (ex X t) : H →ₗ[ℂ] H), hiso _ (hX t)⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  simp only [ex_zero, hσ.map_one, ContinuousLinearMap.one_apply] at h2
  rw [inner_neg_left]
  linear_combination h2
end CompanionTheory.D.gk.FinalFormK
