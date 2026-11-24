-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.needs.orbJ_smul_of_ae
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:08:44.540275+00:00
-- url     : https://prove2.me/submissions/1f877dec-4f00-492d-a40b-0e8f18d72668

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_JCx1_needs_choose_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt Filter Topology MeasureTheory NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.needs
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.JCx1.needs
theorem _root_.solution (Bs : RealPlaceData k r Wp Wq) (γ : Mat k r) (μR : Measure (Mt k r))
    (F G : Mat k r → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hFG : ∀ᵐ p ∂Bs.μSS, D.orbIntegrand Bs γ F p = c • D.orbIntegrand Bs γ G p) :
    D.orbJ Bs γ μR F = c • D.orbJ Bs γ μR G := by
  unfold D.orbJ
  by_cases hc : c = 0
  · subst hc
    rw [zero_smul]
    split_ifs with hF
    · refine (integral_congr_ae ?_).trans (integral_zero _ _)
      exact hFG.mono fun p hp => by simp only [hp, zero_smul, smul_zero]
    all_goals rfl
  · have hiff : ∀ θ : B.SS k r → ℝ, Integrable (fun p => θ p • D.orbIntegrand Bs γ F p) Bs.μSS ↔
        Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := by
      intro θ
      have e : (fun p => θ p • D.orbIntegrand Bs γ F p) =ᵐ[Bs.μSS]
          fun p => c • (θ p • D.orbIntegrand Bs γ G p) :=
        hFG.mono fun p hp => by
          simp only [hp]
          exact smul_comm _ _ _
      rw [integrable_congr e]
      exact integrable_smul_iff hc (fun p => θ p • D.orbIntegrand Bs γ G p)
    split_ifs with hF hG hG
    · rw [choose_congr (by funext θ; exact propext (and_congr_right fun _ => hiff θ)) hF hG,
        ← integral_smul]
      refine integral_congr_ae (hFG.mono fun p hp => ?_)
      simp only [hp]
      exact smul_comm _ _ _
    · exact (hG ⟨hF.choose, hF.choose_spec.1, (hiff _).1 hF.choose_spec.2⟩).elim
    · exact (hF ⟨hG.choose, hG.choose_spec.1, (hiff _).2 hG.choose_spec.2⟩).elim
    · simp
end Formalism.FourierDecayAlt.P.JCx1.needs
