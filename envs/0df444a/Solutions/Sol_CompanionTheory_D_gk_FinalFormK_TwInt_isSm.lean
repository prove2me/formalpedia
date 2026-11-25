-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.TwInt.isSm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:40:54.455804+00:00
-- url     : https://prove2.me/submissions/703b60ab-a390-4aae-837c-1b4e1f14b382

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_congr
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_smOn_orbit
import Theorems.Thm_P2M_CompanionTheory_D_gk_FinalFormK_SmOn_smul__7902115b4004
import Theorems.Thm_P2M_CompanionTheory_D_gk_FinalFormK_SmOn_sum__d3e2bbf2deaa
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_Bdd_smOn_orbit

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → ι → ι → ℂ} {T : ι → H → H'}
omit [DecidableEq ι]
namespace CompanionTheory.D.gk.FinalFormK
namespace TwInt
theorem _root_.solution (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hL : ∀ X, L X → ∀ t, ex X t ∈ G)
    (hM : ∀ c d, SmOn G fun g => M g c d) (c : ι) {v : H} (hv : IsSm G σ v) : IsSm G τ (T c v) :=
  (SmOn.sum' Finset.univ fun d _ => SmOn.smul' (hM c d) ((h.bdd d).smOn_orbit (h.lin d) hσ hL hv)).congr
    fun g hg => h.eqv g hg c v hv
end TwInt
end CompanionTheory.D.gk.FinalFormK
