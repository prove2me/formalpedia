-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.diff_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:30.335722+00:00
-- url     : https://prove2.me/submissions/1e75b462-b792-4949-a248-6ffa192e54cb

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_DB_affine

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
theorem _root_.solution {a b : ℕ} (hcore : CoreProp a b) (m : ℕ) (β D z τ' : ℂ) (y : UT (m + 2) → ℂ) {c Rz K' : ℝ}
    (Φ : Mat (m + 1 + 1) → V) (hc0 : 0 < c) (hRz : 1 ≤ Rz) (hz0 : z ≠ 0) (hzR : ‖z‖ ≤ Rz) (hDR : ‖D‖ ≤ Rz)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (hτ1 : ‖τ'‖ ≤ 1) (hl : c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖)
    (hΦ : DB 1 Φ (MXY m D τ' (fun _ => z, y)) K' 1) :
    DB 1 (fun v : ℂ => ampE β m Φ D v (fun _ => z, y)) τ'
      (K' * (((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) * (1 + ‖y‖) ^ (4 * (m + 2))) ^ a)
      ((((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) * (1 + ‖y‖) ^ (4 * (m + 2))) ^ b) := by
  set cQ : ℝ := 4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖ with hcQ
  set cW : ℝ := cQ ^ (4 * (m + 2)) + 2 / c with hcW
  set Y : ℝ := 1 + ‖y‖ with hY
  have hy0 := norm_nonneg y
  have hY1 : 1 ≤ Y := by linarith
  have hβ0 := norm_nonneg β
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hm2 : (0 : ℝ) ≤ ((m : ℝ) + 2) ^ 2 := by positivity
  have hcQ1 : 1 ≤ cQ := by linarith
  have hcQ0 : 0 ≤ cQ := by linarith
  have h2c : 0 ≤ 2 / c := by positivity
  have hcQp : 0 ≤ cQ ^ (4 * (m + 2)) := by positivity
  have hcW0 : 0 ≤ cW := by linarith
  have hYp : 1 ≤ Y ^ (4 * (m + 2)) := one_le_pow₀ hY1
  have hQ : ∀ r : ℝ, r ≤ cQ → r ≤ cQ * Y := fun r hr =>
    hr.trans (le_mul_of_one_le_right hcQ0 hY1)
  have hW : ∀ r : ℝ, r ≤ cW → r ≤ cW * Y ^ (4 * (m + 2)) := fun r hr =>
    hr.trans (le_mul_of_one_le_right hcW0 hYp)
  have g1 : (2 : ℝ) ^ 1 * ((m : ℝ) + 2) ^ 2 * (Nat.factorial 1 : ℕ) ≤ cQ * Y := by
    refine hQ _ ?_
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, mul_one]
    linarith
  have g2 : DB 1 (fun v : ℂ => v) τ' (cQ * Y) 1 := by
    have h := DB.affine 1 (ContinuousLinearMap.id ℝ ℂ) (0 : ℂ) τ' (S := cQ * Y)
      (by
        simp only [ContinuousLinearMap.id_apply, add_zero]
        exact hQ _ (by linarith))
      (ContinuousLinearMap.norm_id_le.trans (hQ _ hcQ1))
    simpa using h
  have g3 : ∀ _k : Fin (m + 1), DB 1 (fun _ : ℂ => z) τ' (cQ * Y) 1 := fun _ =>
    DB.const 1 z τ' (hQ _ (by linarith)) zero_le_one
  have g4 : ∀ e : UT (m + 2), DB 1 (fun _ : ℂ => y e) τ' (cQ * Y) 1 := fun e => by
    refine DB.const 1 (y e) τ' ((norm_le_pi_norm y e).trans ?_) zero_le_one
    calc ‖y‖ ≤ 1 * Y := by linarith
      _ ≤ cQ * Y := mul_le_mul_of_nonneg_right hcQ1 (by linarith)
  have g5 : ‖D‖ ≤ cQ * Y := hQ _ (by linarith)
  have g6 : ‖β‖ ≤ cQ * Y := hQ _ (by linarith)
  have g7 : (cQ * Y) ^ (4 * (m + 2)) ≤ cW * Y ^ (4 * (m + 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have g8 : cofXY m τ' (fun _ => z, y) ≠ 0 := by
    rw [← norm_pos_iff]
    linarith
  have g9 : ‖cofXY m τ' (fun _ => z, y)‖⁻¹ ≤ cW * Y ^ (4 * (m + 2)) := by
    refine hW _ ?_
    have e1 : ‖cofXY m τ' (fun _ => z, y)‖⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      exact hl
    linarith
  have g10 : ∏ _k : Fin (m + 1), z ≠ 0 := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_ne_zero _ hz0
  have g11 : ‖∏ _k : Fin (m + 1), z‖⁻¹ ≤ cW * Y ^ (4 * (m + 2)) := by
    refine hW _ ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow]
    have e1 : (‖z‖ ^ (m + 1))⁻¹ ≤ 2 / c := by
      rw [inv_le_comm₀ (by linarith) (by positivity), inv_div]
      linarith
    linarith
  exact hcore ℂ m 1 β D (fun v => v) (fun _ _ => z) (fun _ => y) τ' (cQ * Y) (cW * Y ^ (4 * (m + 2)))
    g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 V Φ K' hΦ
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
