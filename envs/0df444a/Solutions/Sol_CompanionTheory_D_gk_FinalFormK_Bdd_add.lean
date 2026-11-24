-- Prove2me | solution 1 for CompanionTheory.D.gk.FinalFormK.Bdd.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:22:09.778319+00:00
-- url     : https://prove2.me/submissions/2567a292-31f6-4c18-a879-c2b6fbab6d67

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_HaarBumpFunctions_ExistsIsBump
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnAdditive
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_OrbitDerivatives_HasDerivAtMatrixExpZero
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_nu_nonneg
import Theorems.Thm_CompanionTheory_D_gk_FinalFormK_nu_append
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_trans


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
theorem _root_.solution {E : Type} [NormedAddCommGroup E] {T T' : H → E} (h : Bdd G L σ T) (h' : Bdd G L σ T') :
    Bdd G L σ fun v => T v + T' v := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  obtain ⟨C', Ws', hW', hb'⟩ := h'
  refine ⟨|C| + |C'|, Ws ++ Ws', fun W hW0 => (List.mem_append.1 hW0).elim (hW W) (hW' W), fun v hv => ?_⟩
  rw [nu_append]
  have h1 := (hb v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (nu_nonneg Ws v))
  have h2 := (hb' v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (nu_nonneg Ws' v))
  nlinarith [norm_add_le (T v) (T' v), mul_nonneg (abs_nonneg C) (nu_nonneg (σ := σ) Ws' v),
    mul_nonneg (abs_nonneg C') (nu_nonneg (σ := σ) Ws v)]
end Bdd
end CompanionTheory.D.gk.FinalFormK
