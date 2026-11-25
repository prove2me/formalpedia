-- Prove2me | solution 1 for Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas.shape
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:26:58.359069+00:00
-- url     : https://prove2.me/submissions/0f130028-25c0-4a47-a8d8-3fb5d62703d9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TwoPlaces
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_SecondLevelOfNorm
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionRelationOfExpSpec
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TwoPlaces
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog bSum idM ZV serAlong HasJetBound OrbitsMul opAlong jetPairPoly)
open Formalism.InvariantFactorPaths.G7 (Simeq UnrOK IsLawOfLog)
open MvPowerSeries
open Formalism.L2.Th1.D Formalism.L2.Th1.D.BiextensionAlongSeries
namespace Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
theorem _root_.solution (hO : OrbitsMul) (K : Type) [NormedField K] [IsUltrametricDist K]
    (ι₁ ι₂ σ₁ σ₂ : Type) [Finite ι₁] [Finite ι₂]
    (g₁ : ι₁ → MvPowerSeries ι₁ K) (g₂ : ι₂ → MvPowerSeries ι₂ K)
    (h₁ : ∀ x, constantCoeff (g₁ x) = 0) (h₂ : ∀ x, constantCoeff (g₂ x) = 0)
    (E₁ : MvPowerSeries ι₁ K) (E₂ : MvPowerSeries ι₂ K)
    (P₁ : MvPolynomial ι₁ (MvPolynomial σ₁ K)) (P₂ : MvPolynomial ι₂ (MvPolynomial σ₂ K))
    (B₁ B₂ : ℝ) (b₁ : HasJetBound g₁ E₁ P₁ B₁) (b₂ : HasJetBound g₂ E₂ P₂ B₂)
    (U Th : MvPowerSeries (ι₁ ⊕ ι₂) K) (hU : Integral U)
    (hTh : Th = subst (Sum.elim (fun x => serAlong Sum.inl (g₁ x))
      (fun x => serAlong Sum.inr (g₂ x))) U * (serAlong Sum.inl E₁ * serAlong Sum.inr E₂))
    (n : σ₁ ⊕ σ₂ →₀ ℕ) :
    ‖MvPolynomial.coeff n (jetPairPoly (opAlong Sum.inl Sum.inl P₁ * opAlong Sum.inr Sum.inr P₂) Th)‖
      ≤ B₁ * B₂ := by
  rw [hTh]
  exact hO K ι₁ ι₂ σ₁ σ₂ g₁ g₂ h₁ h₂ E₁ E₂ P₁ P₂ B₁ B₂ b₁ b₂ U hU n
end Formalism.L2.Th1.D.TwoPlaceCoordinateLemmas
