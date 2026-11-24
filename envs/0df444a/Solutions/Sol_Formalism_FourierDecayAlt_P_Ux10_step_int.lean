-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.step_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:14:26.393044+00:00
-- url     : https://prove2.me/submissions/56c57928-475c-4529-98a9-fa0de9b04f2c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux10_aesm_deriv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_ckOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_cv_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Matrix Filter Topology
open Matrix MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {b : Bool} {X : Mat k r} (hX : inLie k r X) [CompleteSpace E] (ψ : α → ℂ) (hψ : ∀ ξ, ‖ψ ξ‖ ≤ 1)
    (hψm : AEStronglyMeasurable ψ μ) (G : α → Mat k r → E) (hG1 : ∀ ξ, CkOn ((1 : ℕ) : ℕ∞) (GV k r) (G ξ))
    (hGm : ∀ g ∈ GV k r, AEStronglyMeasurable (fun ξ => G ξ g) μ) (β : α → ℝ) (hβ : Integrable β μ)
    (hb0 : ∀ g ∈ GV k r, ∀ ξ, ‖G ξ g‖ ≤ β ξ) (hb1 : ∀ g ∈ GV k r, ∀ ξ, ‖op b X (G ξ) g‖ ≤ β ξ)
    (Φ : Mat k r → E) (hΦ : ∀ g ∈ GV k r, Φ g = ∫ ξ, ψ ξ • G ξ g ∂μ) :
    ∀ g ∈ GV k r, op b X Φ g = ∫ ξ, ψ ξ • op b X (G ξ) g ∂μ := by
  intro g hg
  have hcurve : ∀ t, cv b X t g ∈ GV k r := fun t => cv_mem hX hg t
  have hd : ∀ ξ, ∀ g₁ ∈ GV k r, HasDerivAt (fun s : ℝ => G ξ (cv b X s g₁)) (op b X (G ξ) g₁) 0 :=
    fun ξ g₁ hg₁ => (ckOn_diff 0 b (hG1 ξ) hX hg₁).hasDerivAt
  have hd1m : ∀ g₁ ∈ GV k r, AEStronglyMeasurable (fun ξ => op b X (G ξ) g₁) μ := fun g₁ hg₁ =>
    aesm_deriv (G := fun ξ t => G ξ (cv b X t g₁)) (fun ξ => hd ξ g₁ hg₁)
      (Eventually.of_forall fun t => hGm _ (cv_mem hX hg₁ t))
  have hsm : ∀ ξ (e : E), ‖ψ ξ • e‖ ≤ ‖e‖ := fun ξ e => by
    rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ) (bound := β)
    (F := fun t ξ => ψ ξ • G ξ (cv b X t g)) (x₀ := 0) (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun t => hψm.smul (hGm _ (hcurve t)))
    (hβ.mono' (hψm.smul (hGm _ (hcurve 0))) (Eventually.of_forall fun ξ => (hsm ξ _).trans (hb0 _ (hcurve 0) ξ)))
    (F' := fun t ξ => ψ ξ • op b X (G ξ) (cv b X t g))
    (hψm.smul (hd1m _ (hcurve 0)))
    (Eventually.of_forall fun ξ t _ => (hsm ξ _).trans (hb1 _ (hcurve t) ξ)) hβ
    (Eventually.of_forall fun ξ t _ => by
      have e : (fun t' : ℝ => G ξ (cv b X t' g)) = fun t' => G ξ (cv b X (t' - t) (cv b X t g)) := by
        funext t'; rw [← cv_add]; congr 2; ring
      have h2 : HasDerivAt (fun s => G ξ (cv b X s (cv b X t g))) (op b X (G ξ) (cv b X t g)) (t - t) := by
        rw [sub_self]; exact hd ξ _ (hcurve t)
      have h3 := (h2.comp_sub_const t t)
      rw [← e] at h3
      exact h3.const_smul (ψ ξ))
  have e1 : (fun t : ℝ => Φ (cv b X t g)) = fun t => ∫ ξ, ψ ξ • G ξ (cv b X t g) ∂μ := by
    funext t; exact hΦ _ (hcurve t)
  show deriv (fun t : ℝ => Φ (cv b X t g)) 0 = _
  rw [e1, key.2.deriv]
  simp only [cv_zero]
end Formalism.FourierDecayAlt.P.Ux10
