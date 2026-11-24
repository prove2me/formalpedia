-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.Bdd.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:00:07.140882+00:00
-- url     : https://prove2.me/submissions/9db42d76-1c1e-4332-9768-95e83536933b

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero

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
namespace CompanionTheory.D.gk.FinalFormK
namespace Bdd
theorem _root_.solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : H → E} (h : Bdd G L σ T) (a : ℂ) :
    Bdd G L σ fun v => a • T v := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  refine ⟨‖a‖ * C, Ws, hW, fun v hv => ?_⟩
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb v hv) (norm_nonneg _)
end Bdd
end CompanionTheory.D.gk.FinalFormK
