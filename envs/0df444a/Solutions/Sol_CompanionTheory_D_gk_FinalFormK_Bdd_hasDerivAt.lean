-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.Bdd.hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:44.552458+00:00
-- url     : https://prove2.me/submissions/33b44bf7-747b-4d65-b893-183f8800010c

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_nu_eq_sum
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_exists_factor
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_hasDerivAt_dsW_orbit
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
variable [CompleteSpace H] [CompleteSpace H']
namespace CompanionTheory.D.gk.FinalFormK
namespace Bdd
theorem _root_.solution {T : H → H'} (hb : Bdd G L σ T) (hl : Lin G σ T) (hσ : RepOn G σ)
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v})
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun t => T (σ (ex X t) v)) (T (ds σ X v)) 0 := by
  obtain ⟨C, Ws, hW, hb⟩ := hb
  have hW' : ∀ i, LieW G (Ws.get i) := fun i X hX => hL X (hW _ (List.get_mem _ _) X hX)
  obtain ⟨Λ, hΛ⟩ := exists_factor hl hσ hW' (C := C) fun v hv => by rw [← nu_eq_sum]; exact hb v hv
  have hs : IsSm G σ (ds σ X v) := hv.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
  have e : (fun t => T (σ (ex X t) v)) = fun t => ∑ i, Λ i (dsW σ (Ws.get i) (σ (ex X t) v)) :=
    funext fun t => hΛ _ (hv.apply hσ (hX t))
  rw [e, hΛ _ hs]
  exact HasDerivAt.fun_sum fun i _ => ((Λ i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_dsW_orbit hσ hiso hd hv (hW' i) hX)
end Bdd
end CompanionTheory.D.gk.FinalFormK
