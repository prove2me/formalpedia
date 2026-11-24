-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.Bdd.comp_dsW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:16:56.859987+00:00
-- url     : https://prove2.me/submissions/649ebc99-4921-4099-ba91-da0dd9a5e573

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_dsW_append
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_diag_apply
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans
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
namespace Bdd
theorem _root_.solution {E : Type} [NormedAddCommGroup E] {T : H → E} (h : Bdd G L σ T) (hσ : RepOn G σ)
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {W' : List (Mat n)} (hW' : ∀ X ∈ W', L X) :
    Bdd G L σ fun v => T (dsW σ W' v) := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  refine ⟨C, Ws.map (· ++ W'), fun W hW0 X hX => ?_, fun v hv => ?_⟩
  · obtain ⟨W₀, hW₀, rfl⟩ := List.mem_map.1 hW0
    exact (List.mem_append.1 hX).elim (hW W₀ hW₀ X) (hW' X)
  · refine (hb _ (hv.dsW hσ fun X hX => hL X (hW' X hX))).trans (le_of_eq ?_)
    simp only [nu, List.map_map, Function.comp_def, dsW_append]
end Bdd
end CompanionTheory.D.gk.FinalFormK
