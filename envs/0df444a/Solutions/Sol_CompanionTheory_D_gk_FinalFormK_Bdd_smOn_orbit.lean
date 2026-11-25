-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.Bdd.smOn_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:33:52.479585+00:00
-- url     : https://prove2.me/submissions/648cf787-eec0-4fd4-b616-9a46b8e69dba

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_nu_eq_sum
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_congr
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_exists_factor
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_smOn_orbit
import Theorems.Thm_P2M_CompanionTheory_D_gk_FinalFormK_SmOn_sum__d3e2bbf2deaa
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_clm


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
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : SmOn G fun g => T (σ g v) := by
  obtain ⟨C, Ws, hW, hb⟩ := hb
  have hW' : ∀ i, LieW G (Ws.get i) := fun i X hX => hL X (hW _ (List.get_mem _ _) X hX)
  obtain ⟨Λ, hΛ⟩ := exists_factor hl hσ hW' (C := C) fun v hv => by rw [← nu_eq_sum]; exact hb v hv
  exact (SmOn.sum' Finset.univ fun i _ =>
    (FinalFormK.smOn_orbit hσ hv (hW' i)).clm ((Λ i).restrictScalars ℝ)).congr fun g hg => hΛ _ (hv.apply hσ hg)
end Bdd
end CompanionTheory.D.gk.FinalFormK
