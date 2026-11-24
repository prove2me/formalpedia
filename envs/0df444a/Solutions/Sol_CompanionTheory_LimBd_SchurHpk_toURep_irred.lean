-- Prove2me | solution 1 for CompanionTheory.LimBd.SchurHpk.toURep_irred
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:19:46.607095+00:00
-- url     : https://prove2.me/submissions/a15a5e4e-5a34-4637-b056-2b361a0f07ea

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_exists_iota_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.SchurHpk
open MeasureTheory Matrix Topology PI.UpqRep CompanionTheory.LimBd.URep
open scoped InnerProductSpace ENNReal
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {H' : Type*} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
namespace CompanionTheory.LimBd.SchurHpk
theorem _root_.solution (hP : IsCayley k r ε P)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UH (Hpk k r)) σ) [Nontrivial H] (hi : IsIrredOn (UH (Hpk k r)) σ) :
    (toURep hP σ hσ).IsIrreducible := by
  refine ⟨inferInstance, fun V hV hinv => hi V hV fun x hx v hv => ?_⟩
  obtain ⟨g, rfl⟩ := exists_iota_eq hP hx
  exact hinv g v hv
end CompanionTheory.LimBd.SchurHpk
