-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.diff_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:46.588682+00:00
-- url     : https://prove2.me/submissions/7f3a6ff2-db38-4353-9273-98b3390d83cc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_diff_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
theorem _root_.solution {a b : ℕ} (hcore : CoreProp a b) (m : ℕ) (β D z t : ℂ) (y : UT (m + 2) → ℂ) {c Rz K' : ℝ}
    (Φ : Mat (m + 1 + 1) → V) (hc0 : 0 < c) (hRz : 1 ≤ Rz) (hz0 : z ≠ 0) (hzR : ‖z‖ ≤ Rz) (hDR : ‖D‖ ≤ Rz)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (ht1 : ‖t‖ ≤ 1)
    (hcof : ∀ τ' : ℂ, ‖τ'‖ ≤ ‖t‖ → c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖)
    (hΦ : ∀ τ' : ℂ, ‖τ'‖ ≤ ‖t‖ → DB 1 Φ (MXY m D τ' (fun _ => z, y)) K' 1) :
    ‖ampE β m Φ D t (fun _ => z, y) - ampE β m Φ D 0 (fun _ => z, y)‖ ≤
      K' * ((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) ^ (a + b) *
        (1 + ‖y‖) ^ (4 * (m + 2) * (a + b)) * ‖t‖ := by
  set cW : ℝ := (4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c with hcW
  have key : ∀ τ' ∈ Metric.closedBall (0 : ℂ) ‖t‖,
      DB 1 (fun v : ℂ => ampE β m Φ D v (fun _ => z, y)) τ' (K' * (cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ a)
        ((cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ b) := by
    intro τ' hτ'
    have hτ : ‖τ'‖ ≤ ‖t‖ := by simpa using hτ'
    exact diff_key hcore m β D z τ' y Φ hc0 hRz hz0 hzR hDR hcz (hτ.trans ht1) (hcof τ' hτ) (hΦ τ' hτ)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    (f := fun v : ℂ => ampE β m Φ D v (fun _ => z, y))
    (C := K' * (cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ a * (cW * (1 + ‖y‖) ^ (4 * (m + 2))) ^ b)
    (s := Metric.closedBall (0 : ℂ) ‖t‖) (x := 0) (y := t)
    (fun τ' hτ' => (key τ' hτ').1.differentiableAt (by norm_num))
    (fun τ' hτ' => by
      have h := (key τ' hτ').2 1 le_rfl
      rwa [norm_iteratedFDeriv_one, pow_one] at h)
    (convex_closedBall _ _) (by simp) (by simp)
  rw [sub_zero] at hmv
  refine hmv.trans (le_of_eq ?_)
  rw [mul_assoc K', ← pow_add, mul_pow, ← pow_mul]
  ring
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
