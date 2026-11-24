-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.exists_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:37:14.681805+00:00
-- url     : https://prove2.me/submissions/9a6e905d-d220-41e5-a5a0-616ae73e18ef

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smul
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_inner_ds
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_dsW_cons
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
theorem _root_.solution (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) {W : List (Mat n)} (hW : LieW G W)
    {u : H} (hu : IsSm G σ u) : ∃ u', ∀ v, IsSm G σ v → ⟪u, dsW σ W v⟫_ℂ = ⟪u', v⟫_ℂ := by
  induction W generalizing u with
  | nil => exact ⟨u, fun _ _ => rfl⟩
  | cons X W ih =>
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hX := hW X List.mem_cons_self
    have h1 : IsSm G σ (ds σ X u) := hu.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    obtain ⟨u', hu'⟩ := ih hW' (u := -ds σ X u) (by simpa using h1.smul (-1))
    exact ⟨u', fun v hv => by rw [dsW_cons, inner_ds hσ hiso hu (hv.dsW hσ hW') hX, hu' v hv]⟩
end CompanionTheory.D.gk.FinalFormK
